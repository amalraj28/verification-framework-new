from __future__ import annotations
from copy import deepcopy
from qiskit import QuantumRegister
from qiskit.circuit import Instruction, Gate
from qiskit.dagcircuit import DAGCircuit, DAGOpNode
import random
from typing import Iterable, List, Optional, TypedDict, NotRequired, Dict

# --------- types ---------

class LocationParams(TypedDict):
    gate_name: str
    qubit: int
    occurrence: NotRequired[int]

class CompositeGatesStruct(TypedDict):
    aux: Gate
    res: Gate

SequenceBook = Dict[str, List[List[str]]]

# --------- helpers you already have (or very close) ---------

def qubit_index(qb) -> int:
    return getattr(qb, "index", getattr(qb, "_index"))


def dag_find_kth_gate_on_qubit(
    dag: DAGCircuit,
    gate_name: str,
    qubit: int,
    k: int,
) -> DAGOpNode:
    """
    Returns the DAGOpNode for the k-th occurrence (topological order) of gate_name
    that touches `qubit` (works for multi-qubit gates too).
    """
    if k <= 0:
        raise ValueError("k must be >= 1")

    count = 0
    for node in dag.topological_op_nodes():
        if node.name != gate_name:
            continue
        if any(qubit_index(qb) == qubit for qb in node.qargs):
            count += 1
            if count == k:
                return node

    raise ValueError(f"Did not find {k}-th '{gate_name}' touching qubit {qubit}")


def dag_insert_single_qubit_ops_before_node(
    dag: DAGCircuit,
    target_node: DAGOpNode,
    target_qubit: int,
    ops: Iterable[Instruction],
) -> None:
    ops_list = list(ops)
    for op in ops_list:
        if getattr(op, "num_qubits", None) != 1:
            raise ValueError(f"Only single-qubit insert ops supported, got {op.name}")

    positions = [i for i, qb in enumerate(target_node.qargs) if qubit_index(qb) == target_qubit]

    if not positions:
        raise ValueError(
            f"Target '{target_node.name}' does not touch qubit {target_qubit}. "
            f"qargs={[qubit_index(q) for q in target_node.qargs]}"
        )

    pos = positions[0]
    n = len(target_node.qargs)

    rep_dag = DAGCircuit()
    qreg = QuantumRegister(n, "q")
    rep_dag.add_qreg(qreg)

    for op in ops_list:
        rep_dag.apply_operation_back(op, qargs=[qreg[pos]], cargs=[])

    rep_dag.apply_operation_back(
        target_node.op,
        qargs=[qreg[i] for i in range(n)],
        cargs=list(target_node.cargs),
    )

    wire_map = {qreg[i]: target_node.qargs[i] for i in range(n)}
    dag.substitute_node_with_dag(target_node, rep_dag, wires=wire_map)


def dag_replace_single_qubit_node_with_sequence(
    dag: DAGCircuit,
    target_node: DAGOpNode,
    target_qubit: int,
    ops: Iterable[Instruction],
    require_gate_name: Optional[str] = None,
) -> None:
    if require_gate_name is not None and target_node.name != require_gate_name:
        raise ValueError(f"Expected gate '{require_gate_name}', found '{target_node.name}'")

    if len(target_node.qargs) != 1:
        raise ValueError(
            f"Only single-qubit replacement supported. "
            f"Target '{target_node.name}' acts on {len(target_node.qargs)} qubits."
        )

    if qubit_index(target_node.qargs[0]) != target_qubit:
        raise ValueError(
            f"Target node qubit is {qubit_index(target_node.qargs[0])}, "
            f"but target_qubit={target_qubit}"
        )

    ops_list = list(ops)
    for op in ops_list:
        if getattr(op, "num_qubits", None) != 1:
            raise ValueError(f"Only single-qubit ops supported, got {op.name}")

    rep_dag = DAGCircuit()
    qreg = QuantumRegister(1, "q")
    rep_dag.add_qreg(qreg)
    q0 = qreg[0]

    for op in ops_list:
        rep_dag.apply_operation_back(op, qargs=[q0], cargs=[])

    wire_map = {q0: target_node.qargs[0]}
    dag.substitute_node_with_dag(target_node, rep_dag, wires=wire_map)

# --------- DAG-level obfuscations ---------

def inverseGatesDAG(
    dag: DAGCircuit,
    location_params: LocationParams,
    ops: List[str],
    inverse_pairs: Dict[str, List[type[Instruction]]],
) -> DAGCircuit:
    """
    Insert inverse-pair sequences before a located node, on the specified qubit.
    ops is list of tokens like ["x","y","tdg"] and inverse_pairs maps token -> [GateClass, GateClass]
    """
    gate_name = location_params["gate_name"]
    qubit = location_params["qubit"]
    occurrence = location_params.get("occurrence", 1)

    target_node = dag_find_kth_gate_on_qubit(dag, gate_name, qubit, occurrence)

    insert_ops: List[Instruction] = []
    for token in ops:
        if token not in inverse_pairs:
            raise ValueError(f"Unknown inverse-pair token: {token}")
        for gate_cls in inverse_pairs[token]:
            insert_ops.append(gate_cls())

    dag1 = deepcopy(dag)
    
    dag_insert_single_qubit_ops_before_node(dag1, target_node=target_node, target_qubit=qubit, ops=insert_ops)
    
    return dag1

def compositeGatesDAG(
    dag: DAGCircuit,
    location_params: LocationParams,
    composite_ops: CompositeGatesStruct,
) -> DAGCircuit:
    """
    Insert [aux, res] (both single-qubit Gates) before a located node on the specified qubit.
    """
    gate_name = location_params["gate_name"]
    qubit = location_params["qubit"]
    occurrence = location_params.get("occurrence", 1)

    target_node = dag_find_kth_gate_on_qubit(dag, gate_name, qubit, occurrence)

    insert_ops: List[Instruction] = [composite_ops["aux"], composite_ops["res"]]

    dag1 = deepcopy(dag)
    
    dag_insert_single_qubit_ops_before_node(dag1, target_node=target_node, target_qubit=qubit, ops=insert_ops)
    
    return dag1


def sequenceReplaceGatesDAG(
    dag: DAGCircuit,
    location_params: LocationParams,
    sequence_book: SequenceBook,
    get_single_qubit_ops,  # your function: List[str] -> List[GateClass]
    variant: Optional[int] = None,
) -> DAGCircuit:
    """
    Generic: replace the located single-qubit gate with a chosen recipe sequence.
    Works for cloaked and delayed.
    """
    gate_name = location_params["gate_name"]
    qubit = location_params["qubit"]
    occurrence = location_params.get("occurrence", 1)

    if gate_name not in sequence_book:
        raise ValueError(f"No sequences defined for gate: {gate_name}")

    recipes = sequence_book[gate_name]
    if not recipes:
        raise ValueError(f"Empty sequence list for gate: {gate_name}")

    if variant is None:
        variant = random.randrange(len(recipes))
    
    if variant < 0 or variant >= len(recipes):
        raise IndexError(f"variant must be in [0, {len(recipes)-1}], got {variant}")

    target_node = dag_find_kth_gate_on_qubit(dag, gate_name, qubit, occurrence)

    seq_names = recipes[variant]
    gate_classes = get_single_qubit_ops(seq_names)   # returns constructors/classes
    replace_ops: List[Instruction] = [gate() for gate in gate_classes]

    dag1 = deepcopy(dag)
    
    dag_replace_single_qubit_node_with_sequence(
        dag1,
        target_node=target_node,
        target_qubit=qubit,
        ops=replace_ops,
        require_gate_name=gate_name,
    )
    
    return dag1


def cloakedGatesDAG(
    dag: DAGCircuit,
    location_params: LocationParams,
    cloaked_gates_sequences: SequenceBook,
    get_single_qubit_ops,
    variant: Optional[int] = None,
) -> DAGCircuit:
    return sequenceReplaceGatesDAG(dag, location_params, cloaked_gates_sequences, get_single_qubit_ops, variant)


def delayedGatesDAG(
    dag: DAGCircuit,
    location_params: LocationParams,
    delayed_gates_sequences: SequenceBook,
    get_single_qubit_ops,
    variant: Optional[int] = None,
) -> DAGCircuit:
    return sequenceReplaceGatesDAG(dag, location_params, delayed_gates_sequences, get_single_qubit_ops, variant)


if __name__ == "__main__":
    from qiskit import QuantumCircuit
    from qiskit.converters import circuit_to_dag
    from qiskit.visualization import dag_drawer
    import matplotlib.pyplot as plt

    from sequences import (
        inverse_pairs,
        cloaked_gates_sequences,
        delayed_gates_sequences,
        get_single_qubit_ops,
    )

    # ----- helper for quick visualization -----

    def show_dag(dag, title=""):
        print(title)
        for i, node in enumerate(dag.topological_op_nodes()):
            print(f"{i}: {node.name} on {[qubit_index(q) for q in node.qargs]}")
        fig = dag_drawer(dag)
        plt.imshow(fig)
        plt.axis("off")
        plt.show()

    # ----- build sample circuit -----
    plt.show(block=False)
    qc = QuantumCircuit(3)
    qc.h(0)
    qc.x(1)
    qc.cx(1, 2)
    qc.y(1)

    dag = circuit_to_dag(qc)

    show_dag(dag, "\nOriginal DAG")

    # ----- inverse gates DAG -----

    dag2 = inverseGatesDAG(
        dag,
        {"gate_name": "x", "qubit": 1, "occurrence": 1},
        ops=["h", "h"],
        inverse_pairs={
            k: [get_single_qubit_ops(v)[0], get_single_qubit_ops(v)[1]]
            for k, v in inverse_pairs.items()
        },
    )

    show_dag(dag2, "\nAfter inverseGatesDAG")

    # ----- cloaked gates DAG -----

    dag3 = cloakedGatesDAG(
        dag,
        {"gate_name": "y", "qubit": 1, "occurrence": 1},
        cloaked_gates_sequences,
        get_single_qubit_ops,
    )

    show_dag(dag3, "\nAfter cloakedGatesDAG")

    # ----- delayed gates DAG -----

    dag4 = delayedGatesDAG(
        dag,
        {"gate_name": "h", "qubit": 0, "occurrence": 1},
        delayed_gates_sequences,
        get_single_qubit_ops,
    )

    show_dag(dag4, "\nAfter delayedGatesDAG")

    plt.show()

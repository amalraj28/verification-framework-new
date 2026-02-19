from qiskit import QuantumCircuit
from qiskit.converters import circuit_to_dag
from qiskit.visualization import dag_drawer
import matplotlib.pyplot as plt
from copy import deepcopy
from qiskit import QuantumRegister
from qiskit.circuit import Instruction, Gate
from qiskit.dagcircuit import DAGCircuit, DAGOpNode
import random
from typing import Iterable, List, Optional, TypedDict, Dict
from sequences import (
    get_single_qubit_ops,
    inverse_pairs,
    composite_gate_sequences,
    cloaked_gates_sequences,
    delayed_gates_sequences,
)

# --------- types ---------


class LocationParams(TypedDict):
    qubit: int
    index: int


class CompositeGatesStruct(TypedDict):
    aux: Gate
    res: Gate


SequenceBook = Dict[str, List[List[str]]]

# --------- helpers you already have (or very close) ---------


def qubit_index(qb) -> int:
    return getattr(qb, "index", getattr(qb, "_index"))


def dag_get_node_at_index_on_qubit(
    dag: DAGCircuit,
    qubit: int,
    index: int,
) -> Optional[DAGOpNode]:
    """
    Returns the DAGOpNode for the i-th operation (topological order) on the specified qubit.
    If index >= number of gates on that qubit, returns None (representing the end of the wire).
    """
    if index < 0:
        raise ValueError("index must be >= 0")

    count = 0
    for node in dag.topological_op_nodes():
        if any(qubit_index(qb) == qubit for qb in node.qargs):
            if count == index:
                return node
            count += 1

    return None


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

    positions = [
        i for i, qb in enumerate(target_node.qargs) if qubit_index(qb) == target_qubit
    ]

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
        raise ValueError(
            f"Expected gate '{require_gate_name}', found '{target_node.name}'"
        )

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
    Insert inverse-pair sequences at a located index on the specified qubit.
    """
    qubit = location_params["qubit"]
    index = location_params["index"]

    insert_ops: List[Instruction] = []
    for token in ops:
        if token not in inverse_pairs:
            raise ValueError(f"Unknown inverse-pair token: {token}")
        for gate_cls in inverse_pairs[token]:
            insert_ops.append(gate_cls())

    dag1 = deepcopy(dag)
    target_node = dag_get_node_at_index_on_qubit(dag1, qubit, index)

    if target_node is None:
        # Insert at the end of the wire
        qarg = dag1.qubits[qubit]
        for op in insert_ops:
            dag1.apply_operation_back(op, qargs=[qarg], cargs=[])
    else:
        dag_insert_single_qubit_ops_before_node(
            dag1, target_node=target_node, target_qubit=qubit, ops=insert_ops
        )

    return dag1


def compositeGatesDAG(
    dag: DAGCircuit,
    location_params: LocationParams,
    composite_ops: CompositeGatesStruct,
) -> DAGCircuit:
    """
    Insert [aux, res] before a located index on the specified qubit.
    """
    qubit = location_params["qubit"]
    index = location_params["index"]

    insert_ops: List[Instruction] = [composite_ops["aux"], composite_ops["res"]]

    dag1 = deepcopy(dag)
    target_node = dag_get_node_at_index_on_qubit(dag1, qubit, index)

    if target_node is None:
        # Insert at the end
        qarg = dag1.qubits[qubit]
        for op in insert_ops:
            dag1.apply_operation_back(op, qargs=[qarg], cargs=[])
    else:
        dag_insert_single_qubit_ops_before_node(
            dag1, target_node=target_node, target_qubit=qubit, ops=insert_ops
        )

    return dag1


def sequenceReplaceGatesDAG(
    dag: DAGCircuit,
    location_params: LocationParams,
    sequence_book: SequenceBook,
    variant: Optional[int] = None,
) -> DAGCircuit:
    """
    Replace the gate at the specified index on the specified qubit with a chosen recipe sequence.
    """
    qubit = location_params["qubit"]
    index = location_params["index"]

    dag1 = deepcopy(dag)
    target_node = dag_get_node_at_index_on_qubit(dag1, qubit, index)

    if target_node is None:
        # If at the end, we can't 'replace' anything, but per user request, we can 'insert' at the end.
        # However, for cloak/delay, we need a gate name to find a sequence.
        # If we treat it as an insertion, what gate are we inserting?
        # Typically cloak/delay replaces an existing gate.
        # For now, if index is out of bounds for replacement, we might error or just skip.
        # Given "If index is more than... inserted at the end", let's see.
        # If we don't have a gate to replace, we can't look up sequence_book.
        raise ValueError(f"No gate found at index {index} on qubit {qubit} to replace.")

    gate_name = target_node.name
    if gate_name not in sequence_book:
        raise ValueError(f"No sequences defined for gate: {gate_name}")

    recipes = sequence_book[gate_name]
    if not recipes:
        raise ValueError(f"Empty sequence list for gate: {gate_name}")

    if variant is not None and not isinstance(variant, int):
        raise TypeError(f"variant must be int or None, got {type(variant)}")

    if variant is None:
        variant = random.randrange(len(recipes))

    if variant < 0 or variant >= len(recipes):
        raise IndexError(f"variant must be in [0, {len(recipes) - 1}], got {variant}")

    seq_names = recipes[variant]
    gate_classes = get_single_qubit_ops(seq_names)  # returns constructors/classes
    replace_ops: List[Instruction] = [gate() for gate in gate_classes]

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
    variant: Optional[int] = None,
) -> DAGCircuit:
    return sequenceReplaceGatesDAG(
        dag, location_params, cloaked_gates_sequences, variant
    )


def delayedGatesDAG(
    dag: DAGCircuit,
    location_params: LocationParams,
    delayed_gates_sequences: SequenceBook,
    variant: Optional[int] = None,
) -> DAGCircuit:
    return sequenceReplaceGatesDAG(
        dag, location_params, delayed_gates_sequences, variant
    )


def show_dag(dag: DAGCircuit, title: str = "", block: bool = True):
    for i, node in enumerate(dag.topological_op_nodes()):
        print(f"{i}: {node.name} on {[qubit_index(q) for q in node.qargs]}")

    # Open a new figure window for each DAG
    plt.figure(num=title)
    fig = dag_drawer(dag)
    plt.imshow(fig)
    plt.axis("off")
    plt.title(title)

    # Use the block parameter correctly
    plt.show(block=block)

    # If not blocking, pause briefly to allow the GUI to process events and render the window
    if not block:
        plt.pause(0.1)


if __name__ == "__main__":
    # ----- helper for quick visualization -----

    # Enable interactive mode for matplotlib
    plt.ion()

    # ----- build sample circuit -----
    qc = QuantumCircuit(3)
    qc.h(0)
    qc.x(1)
    qc.cx(1, 2)
    qc.y(1)

    qc.draw("mpl")
    plt.show(block=False)
    plt.pause(0.1)

    dag = circuit_to_dag(qc)

    show_dag(dag, "\nOriginal DAG", block=False)

    # ----- inverse gates DAG -----

    dag2 = inverseGatesDAG(
        dag,
        {"qubit": 1, "index": 0},
        ops=["h", "h"],
        inverse_pairs={
            k: [get_single_qubit_ops(v)[0], get_single_qubit_ops(v)[1]]
            for k, v in inverse_pairs.items()
        },
    )

    show_dag(dag2, "\nAfter inverseGatesDAG (index 0 on q1)", block=False)

    dag5 = compositeGatesDAG(
        dag,
        {"qubit": 1, "index": 10},  # Out of bounds, should insert at end
        composite_ops=composite_gate_sequences,
    )

    show_dag(dag5, "\nAfter compositeGatesDAG (index 10 on q1 -> end)", block=False)

    # ----- cloaked gates DAG -----

    dag3 = cloakedGatesDAG(
        dag,
        {"qubit": 1, "index": 2},  # Should be the CX or Y
        cloaked_gates_sequences,
    )

    show_dag(dag3, "\nAfter cloakedGatesDAG (index 2 on q1)", block=False)

    # ----- delayed gates DAG -----

    dag4 = delayedGatesDAG(
        dag,
        {"qubit": 0, "index": 0},  # The H gate
        delayed_gates_sequences,
    )

    show_dag(dag4, "\nAfter delayedGatesDAG (index 0 on q0)", block=False)

    print("\nAll plots generated. Keeping windows open...")
    # Final blocking call to keep all windows open until the user closes them
    plt.ioff()  # Turn off interactive mode so plt.show() blocks
    plt.show()

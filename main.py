from copy import deepcopy
import matplotlib.pyplot as plt
from qiskit import QuantumCircuit
from qiskit.circuit import Instruction, CircuitInstruction, Qubit, Gate
from qiskit.dagcircuit import DAGCircuit, DAGDependency
from qiskit.visualization import dag_drawer
import random
from sequences import inverse_pairs, composite_gate_sequences, cloaked_gates_sequences, get_single_qubit_ops, delayed_gates_sequences
from typing import Optional, Iterable, List, TypedDict, Dict


def get_circuit() -> QuantumCircuit:
    qc = QuantumCircuit(5, 1)
    qc.h(0)
    qc.x(1)
    qc.y(2)
    qc.x(3)
    qc.h(4)
    qc.cz(1, 2)
    qc.cx(0, 1)
    qc.cx(3, 4)
    qc.h(3)
    qc.cy(3, 1)
    qc.cx(2, 4)
    
    # qc.measure(0, 0)

    return qc

def draw_qc(qc: QuantumCircuit, output: str = 'mpl', filename: Optional[str] = None, block: bool = True, title: str = ""):
    qc.draw(output=output, filename=filename)
    plt.title(title)
    plt.show(block=block)


def plot_dag(dag: DAGCircuit | DAGDependency, filename: Optional[str] = None):
    fig = dag_drawer(dag, filename=filename)
    plt.imshow(fig)
    plt.axis("off")
    plt.show()


def print_dag_data(dag: DAGCircuit):
    data = dag.topological_op_nodes()

    for i, node in enumerate(data):
        print(f"{i}: {node.name} on {[q._index for q in node.qargs]}")


def qubit_index(qubit) -> int:
    # Works across versions
    return getattr(qubit, "index", getattr(qubit, "_index"))


def find_kth_gate_on_qubit(qc: QuantumCircuit, gate_name: str, qubit: int, k: int) -> int:
    """
    Returns the position in qc.data for the k-th occurrence of `gate_name`
    acting on qubit `q`. Raises if not found.
    """
    if k <= 0:
        raise ValueError("k must be >= 1")

    count = 0
    
    for i, ci in enumerate(qc.data):
        op = ci.operation
        qubits = ci.qubits  # qubits is a tuple, with each entry being of type Qubit, denoting the qubit index on which the gate is acting. Length = Number of qubits the gate is acting on

        if op.name == gate_name and any(qubit_index(qb) == qubit for qb in qubits): 
            count += 1
            
            if count == k:
                return i

    raise ValueError(f"Did not find {k}-th '{gate_name}' on qubit {qubit}")


def count_ops_on_qubit_before_index(qc: QuantumCircuit, qubit: int, end_idx: int) -> int:
    count = 0
    for ci in qc.data[:end_idx]:
        if any(qubit_index(qb) == qubit for qb in ci.qubits):
            count += 1
    return count


def resolve_insert_position_for_qubit(
    qc: QuantumCircuit,
    qubit: int,
    insert_idx_on_qubit: Optional[int],
) -> int:
    if insert_idx_on_qubit is None:
        try:
            return find_kth_gate_on_qubit(qc, "measure", qubit, 1)
        except ValueError:
            return len(qc.data)

    if insert_idx_on_qubit < 0:
        raise IndexError(
            f"insert_idx (on qubit) must be >= 0 or None, got {insert_idx_on_qubit}"
        )

    count = 0
    for i, ci in enumerate(qc.data):
        if any(qubit_index(qb) == qubit for qb in ci.qubits):
            if count == insert_idx_on_qubit:
                return i
            count += 1

    try:
        return find_kth_gate_on_qubit(qc, "measure", qubit, 1)
    except ValueError:
        return len(qc.data)


def insert_single_qubit_ops_at_position(
    qc: QuantumCircuit,
    insert_idx: int,
    qubit: int,
    ops: Iterable[Instruction],
) -> None:
    if insert_idx < 0 or insert_idx > len(qc.data):
        raise IndexError(f"insert_idx must be in [0, {len(qc.data)}], got {insert_idx}")

    q = qc.qubits[qubit]
    for offset, op in enumerate(list(ops)):
        ci = CircuitInstruction(op, qubits=(q,), clbits=())
        qc.data.insert(insert_idx + offset, ci)


def insert_single_qubit_ops_at(
    qc: QuantumCircuit,
    insert_idx: Optional[int],
    qubit: int,
    ops: Iterable[Instruction],
) -> None:
    ops_list: List[Instruction] = list(ops)

    # Edge case checks
    if qubit < 0 or qubit >= qc.num_qubits:
        raise IndexError(f"qubit must be in [0, {qc.num_qubits-1}], got {qubit}")

    insert_pos = resolve_insert_position_for_qubit(qc, qubit, insert_idx)

    for op in ops_list:
        if getattr(op, "num_qubits", None) != 1:
            raise ValueError(f"Only single-qubit ops allowed, got {op.name} with num_qubits={op.num_qubits}")

    insert_single_qubit_ops_at_position(
        qc, insert_idx=insert_pos, qubit=qubit, ops=ops_list
    )


def pop_single_qubit_op_at(
    qc: QuantumCircuit,
    idx: int,
    require_gate_name: Optional[str] = None,
) -> Qubit:
    """
    Removes qc.data[idx]. Returns the qubit it acted on.
    Only supports popping a single-qubit operation.
    """
    if idx < 0 or idx >= len(qc.data):
        raise IndexError(f"idx must be in [0, {len(qc.data)-1}], got {idx}")

    ci = qc.data[idx]
    op = ci.operation
    qubits = ci.qubits

    if require_gate_name is not None and op.name != require_gate_name:
        raise ValueError(
            f"Expected gate '{require_gate_name}' at idx={idx}, found '{op.name}'"
        )

    if len(qubits) != 1:
        raise ValueError(
            f"Only single-qubit pop supported. Gate at idx={idx} acts on {len(qubits)} qubits."
        )

    target_qubit = qubits[0]
    qc.data.pop(idx)

    return target_qubit


def replace_single_qubit_ops_at(
    qc: QuantumCircuit,
    idx: int,
    ops: Iterable[Instruction],
    require_gate_name: Optional[str] = None,
) -> None:
    target_qubit_obj = pop_single_qubit_op_at(
        qc, idx, require_gate_name=require_gate_name
    )

    # convert qubit object -> index
    q_idx = getattr(target_qubit_obj, "index", getattr(target_qubit_obj, "_index"))

    ops_list: List[Instruction] = list(ops)
    for op in ops_list:
        if getattr(op, "num_qubits", None) != 1:
            raise ValueError(f"Only single-qubit ops allowed, got {op.name} with num_qubits={op.num_qubits}")

    insert_single_qubit_ops_at_position(qc, insert_idx=idx, qubit=q_idx, ops=ops_list)


class LocationParams(TypedDict):
    qubit: int # make qubit List[int] for multi-qubit gates
    index: int

class CompositeGatesStruct(TypedDict):
    aux: Gate
    res: Gate


SequenceBook = Dict[str, List[List[str]]]


def find_global_op_position_for_qubit_index(
    qc: QuantumCircuit,
    qubit: int,
    index_on_qubit: int,
) -> Optional[int]:
    if index_on_qubit < 0:
        raise IndexError(f"index must be >= 0, got {index_on_qubit}")

    count = 0
    for i, ci in enumerate(qc.data):
        if any(qubit_index(qb) == qubit for qb in ci.qubits):
            if count == index_on_qubit:
                return i
            count += 1
    return None


def sequenceReplaceGates(qc: QuantumCircuit, location_params: LocationParams, sequence_book: SequenceBook, variant: Optional[int] = None) -> QuantumCircuit:
    qubit = location_params["qubit"]
    idx_on_qubit = location_params["index"]
    idx = find_global_op_position_for_qubit_index(qc, qubit, idx_on_qubit)
    if idx is None:
        raise Exception(
            f"Invalid replacement index: {idx_on_qubit}. Must be < number of ops on qubit {qubit}"
        )

    gate_name = qc.data[idx].operation.name

    if gate_name not in sequence_book:
        raise ValueError(f"No sequences defined for gate: {gate_name}")

    recipes = sequence_book[gate_name]

    if not recipes:
        raise ValueError(f"Empty sequence list for gate: {gate_name}")

    if variant is None:
        variant = random.randrange(len(recipes))

    if not isinstance(variant, int) or variant < 0 or variant >= len(recipes):
        raise IndexError(f"variant must be in [0, {len(recipes)-1}], got {variant}")

    seq_names = recipes[variant]
    gate_classes = get_single_qubit_ops(seq_names)     # returns constructors/classes
    ops = [cls() for cls in gate_classes]              # instantiate here

    qc1 = deepcopy(qc)

    replace_single_qubit_ops_at(qc1, idx, ops=ops)

    return qc1


def inverseGates(qc: QuantumCircuit, location_params: LocationParams, ops: List[str]):
    qubit = location_params['qubit']
    idx = location_params["index"]
    
    if not isinstance(idx, int) or idx < 0: 
        raise ValueError("index should be a non-negative integer, received {idx}")
    
    operators = []
    
    for token in ops:
        if token not in inverse_pairs:
            raise ValueError(f"Unknown inverse-pair token: {token}")
        
        gate_classes = get_single_qubit_ops(inverse_pairs[token])

        for gate in gate_classes:
            operators.append(gate())
    
    qc1 = deepcopy(qc)
    
    insert_single_qubit_ops_at(qc1, idx, qubit, ops=operators)
    
    return qc1


def compositeGates(qc: QuantumCircuit, location_params: LocationParams, ops: CompositeGatesStruct): 
    qubit = location_params['qubit']
    idx = location_params["index"]
    
    if not isinstance(idx, int) or idx < 0: 
        raise ValueError("index should be a non-negative integer, received {idx}")
    
    operators = [ops["aux"], ops["res"]]
    
    qc1 = deepcopy(qc)
    
    insert_single_qubit_ops_at(qc1, idx, qubit, ops=operators)
    
    return qc1


def cloakedGates(qc: QuantumCircuit, location_params: LocationParams, variant: Optional[int] = 0) -> QuantumCircuit:
    return sequenceReplaceGates(qc, location_params, cloaked_gates_sequences, variant)


def delayedGates(qc: QuantumCircuit, location_params: LocationParams, variant: Optional[int] = 0) -> QuantumCircuit:
    return sequenceReplaceGates(qc, location_params, delayed_gates_sequences, variant)


qc = get_circuit()
draw_qc(qc, block=True)

qc1 = inverseGates(qc, {"qubit": 1, "index": 1}, ["h", "t", "s"])
draw_qc(qc1, block=False, title="Inverse Gates")

qc2 = compositeGates(qc, {"qubit": 1, "index": 5}, composite_gate_sequences) # type: ignore
draw_qc(qc2, block=False, title="Composite Gates")

qc3 = cloakedGates(qc, {"qubit": 2, "index": 0})
draw_qc(qc3, block=False, title="Cloaked Gates")

qc4 = delayedGates(qc, {"qubit": 3, "index": 2})
draw_qc(qc4, title="Delayed Gates")

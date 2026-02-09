from copy import deepcopy
from qiskit import QuantumCircuit
from qiskit.circuit import Instruction, CircuitInstruction, Qubit, Gate
from qiskit.converters import circuit_to_dag
from qiskit.dagcircuit import DAGCircuit, DAGDependency
from qiskit.visualization import dag_drawer
import matplotlib.pyplot as plt
from typing import Optional, Iterable, List, TypedDict, NotRequired
from sequences import inverse_pairs, compositeGateSequences


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

def draw_qc(qc: QuantumCircuit, output: str = 'mpl', filename: Optional[str] = None, block: bool = True):
    qc.draw(output=output, filename=filename)
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
    Returns the global index i into qc.data for the k-th occurrence of `gate_name`
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

    # Normalize None to "append before the first measurement"
    if insert_idx is None:
        try:
            insert_idx = find_kth_gate_on_qubit(qc, "measure", qubit, 1)
        except ValueError:
            insert_idx = len(qc.data) # simply append if there is no measurement

    if insert_idx < 0 or insert_idx > len(qc.data):
        raise IndexError(f"insert_idx must be in [0, {len(qc.data)}] or None, got {insert_idx}")

    for op in ops_list:
        if getattr(op, "num_qubits", None) != 1:
            raise ValueError(f"Only single-qubit ops allowed, got {op.name} with num_qubits={op.num_qubits}")

    # Insert ops
    q = qc.qubits[qubit]
    
    for offset, op in enumerate(ops_list):
        ci = CircuitInstruction(op, qubits=(q,), clbits=())
        qc.data.insert(insert_idx + offset, ci)


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

    # convert qubit object -> index for your insert function
    q_idx = getattr(target_qubit_obj, "index", getattr(target_qubit_obj, "_index"))

    insert_single_qubit_ops_at(qc, insert_idx=idx, qubit=q_idx, ops=ops)


class LocationParams(TypedDict):
    gate_name: str
    qubit: int # make qubit List[int] for multi-qubit gates
    occurrence: NotRequired[int]

class CompositeGatesStruct(TypedDict):
    aux: Gate
    res: Gate


def inverseGates(qc: QuantumCircuit, location_params: LocationParams, ops: List[str]): 
    gate_name = location_params['gate_name']
    qubit = location_params['qubit']
    occurrence = location_params.get('occurrence', 1)
    idx = find_kth_gate_on_qubit(qc, gate_name, qubit, occurrence)
    
    operators = []
    
    for token in ops:
        if token not in inverse_pairs:
            raise ValueError(f"Unknown inverse-pair token: {token}")
        
        for gate in inverse_pairs[token]:
            operators.append(gate())
    
    qc1 = deepcopy(qc)
    
    insert_single_qubit_ops_at(qc1, idx, qubit, ops=operators)
    
    return qc1


def compositeGates(qc: QuantumCircuit, location_params: LocationParams, ops: CompositeGatesStruct): 
    gate_name = location_params['gate_name']
    qubit = location_params['qubit']
    occurrence = location_params.get('occurrence', 1)
    idx = find_kth_gate_on_qubit(qc, gate_name, qubit, occurrence)
    
    operators = [ops["aux"], ops["res"]]
    
    qc1 = deepcopy(qc)
    
    insert_single_qubit_ops_at(qc1, idx, qubit, ops=operators)
    
    return qc1


qc = get_circuit()
draw_qc(qc)


qc1 = compositeGates(qc, {"gate_name": "cz", "qubit": 1, "occurrence": 1}, compositeGateSequences) # type: ignore
draw_qc(qc1)

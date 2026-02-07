from qiskit import QuantumCircuit
from qiskit.circuit import Instruction,CircuitInstruction
from qiskit.circuit.library import HGate, RZGate
from qiskit.converters import circuit_to_dag
from qiskit.dagcircuit import DAGCircuit, DAGDependency
from qiskit.visualization import dag_drawer
import matplotlib.pyplot as plt
from typing import Optional, Iterable, List


def get_circuit() -> QuantumCircuit:
    qc = QuantumCircuit(5, 0)
    qc.h(0)
    qc.x(1)
    qc.y(2)
    qc.x(3)
    qc.h(4)
    qc.cz(1,2)
    qc.cx(0,1)
    qc.cx(3,4)
    qc.h(3)
    qc.cy(3,1)
    qc.cx(2,4)
    
    return qc


def plot_dag(dag: DAGCircuit | DAGDependency, filename: Optional[str] = None):
    fig = dag_drawer(dag, filename=filename)
    plt.imshow(fig)
    plt.axis('off')
    plt.show()


def print_dag_data(dag: DAGCircuit):
    data = dag.topological_op_nodes()

    for i, node in enumerate(data):
        print(f"{i}: {node.name} on {[q._index for q in node.qargs]}")


def qubit_index(qubit) -> int:
    # Works across versions
    return getattr(qubit, "index", getattr(qubit, "_index"))


def find_kth_gate_on_qubit(qc: QuantumCircuit, gate_name: str, q: int, k: int) -> int:
    """
    Returns the global index i into qc.data for the k-th occurrence of `gate_name`
    acting on qubit `q`. Raises if not found.
    """
    if k <= 0:
        raise ValueError("k must be >= 1")

    count = 0
    for i, data in enumerate(qc.data):
        op = data.operation
        qubits = data.qubits # qubits is a tuple, with each entry being of type Qubit, denoting the qubit index on which the gate is acting. Length = Number of qubits the gate is acting on
        
        # Since you're focusing on single-qubit gates only:
        if len(qubits) != 1:
            continue

        if qubit_index(qubits[0]) == q and op.name == gate_name:
            count += 1
            if count == k:
                return i

    raise ValueError(f"Did not find {k}-th '{gate_name}' on qubit {q}")


def insert_single_qubit_ops_at(
    qc: QuantumCircuit,
    insert_idx: int,
    qubit: int,
    ops: Iterable[Instruction],
) -> None:
    ops_list: List[Instruction] = list(ops)

    # ************** Edge case checks begin *********************
    
    if insert_idx < 0 or insert_idx > len(qc.data):
        raise IndexError(f"insert_idx must be in [0, {len(qc.data)}], got {insert_idx}")

    if qubit < 0 or qubit >= qc.num_qubits:
        raise IndexError(f"qubit must be in [0, {qc.num_qubits-1}], got {qubit}")

    for op in ops_list:
        if getattr(op, "num_qubits", None) != 1:
            raise ValueError(f"Only single-qubit ops allowed, got {op.name} with num_qubits={op.num_qubits}")
    
    # ************** Edge case checks end *********************

    # Get the data at the required qubit
    q = qc.qubits[qubit]

    for offset, op in enumerate(ops_list):
        ci = CircuitInstruction(op, qubits=(q,), clbits=())
        qc.data.insert(insert_idx + offset, ci) # Adding offset because each insertion will increase the insert_idx by 1


qc = get_circuit()
# qc.draw('mpl')
# plt.show()

# dag = circuit_to_dag(qc)
# plot_dag(dag)

# print_dag_data(dag)

# for i, data in enumerate(qc.data):
#     op = data.operation
#     qubits = data.qubits
#     clbits = data.clbits
    
#     print(f"{i}: {op.name} on {[q._index for q in qubits]}")



idx = find_kth_gate_on_qubit(qc, gate_name="h", q=3, k=1)
print("k-th gate index in qc.data:", idx, qc.data[idx].operation.name)
insert_single_qubit_ops_at(qc, insert_idx=5, qubit=1, ops=[HGate(), RZGate(0.3), HGate()])

qc.draw('mpl')
plt.show()

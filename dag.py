from qiskit.converters import circuit_to_dag
from qiskit.dagcircuit import DAGCircuit, DAGDependency, DAGOpNode
from qiskit.visualization import dag_drawer
from qiskit import QuantumCircuit
import matplotlib.pyplot as plt
from typing import Optional, Iterable, List
from qiskit.circuit import Instruction


def qubit_index(qubit) -> int:
    # Works across versions
    return getattr(qubit, "index", getattr(qubit, "_index"))


def plot_dag(dag: DAGCircuit | DAGDependency, filename: Optional[str] = None):
    fig = dag_drawer(dag, filename=filename)
    plt.imshow(fig)
    plt.axis("off")
    plt.show()


def print_dag_data(dag: DAGCircuit):
    data = dag.topological_op_nodes()

    for i, node in enumerate(data):
        print(f"{i}: {node.name} on {[q._index for q in node.qargs]}")


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
    """
    Inserts the given single-qubit ops BEFORE `target_node` on the wire `target_qubit`.

    Implementation: substitute target_node with a small DAG:
      (ops on selected wire) ; (original target_node op)
    """
    ops_list: List[Instruction] = list(ops)
    for op in ops_list:
        if getattr(op, "num_qubits", None) != 1:
            raise ValueError(f"Only single-qubit insert ops supported, got {op.name}")

    # Identify which position inside target_node.qargs corresponds to target_qubit
    positions = [i for i, qb in enumerate(target_node.qargs) if qubit_index(qb) == target_qubit]
    if not positions:
        raise ValueError(
            f"Target '{target_node.name}' does not touch qubit {target_qubit}. "
            f"Target qargs = {[qubit_index(q) for q in target_node.qargs]}"
        )

    # If target_node touches the same qubit multiple times (rare), pick the first.
    pos = positions[0]

    # Build a replacement circuit with the SAME number of qubits as target_node.qargs
    # so we can map replacement wires -> original wires easily.
    n = len(target_node.qargs)
    rep = QuantumCircuit(n)

    # Apply inserted ops on the chosen wire index `pos`
    for op in ops_list:
        rep.append(op, [pos])

    # Re-append the original target_node operation (preserving qargs order)
    rep.append(target_node.op, list(range(n)))

    rep_dag = circuit_to_dag(rep)

    # Map replacement wires to original wires: qubits then clbits
    # For most gates, cargs is empty, but this keeps it correct if needed.
    wire_map = list(target_node.qargs) + list(target_node.cargs)

    dag.substitute_node_with_dag(target_node, rep_dag, wires=wire_map)


# qc = QuantumCircuit(2)
# qc.h(0)
# qc.cx(0, 1)

# dag = circuit_to_dag(qc)
# print_dag_data(dag)
# plot_dag(dag)

if __name__ == "__main__":
    from qiskit.circuit.library import HGate

    qc = QuantumCircuit(2)
    qc.h(0)
    qc.cx(0, 1)

    dag = circuit_to_dag(qc)

    print("Original DAG:")
    print_dag_data(dag)
    plot_dag(dag)

    # Insert H before the first cx, on qubit 1 (target wire)
    anchor = dag_find_kth_gate_on_qubit(dag, "cx", qubit=1, k=1)
    dag_insert_single_qubit_ops_before_node(dag, anchor, target_qubit=1, ops=[HGate()])

    print("\nModified DAG:")
    print_dag_data(dag)
    plot_dag(dag)
from qiskit import QuantumCircuit
import matplotlib.pyplot as plt
from qiskit.converters import circuit_to_dag
from qiskit.visualization import dag_drawer
from qiskit.dagcircuit import DAGCircuit, DAGDependency
from typing import Optional


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


qc = get_circuit()

dag = circuit_to_dag(qc)
plot_dag(dag)

print_dag_data(dag)

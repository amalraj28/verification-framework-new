from qiskit import QuantumCircuit
import matplotlib.pyplot as plt
from qiskit.converters import circuit_to_dag
from qiskit.visualization import dag_drawer

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


# plt.show()

dag = circuit_to_dag(qc)
fig = dag_drawer(dag)
plt.imshow(fig)
plt.axis('off')
# plt.show()

data = dag.topological_op_nodes()

for i, node in enumerate(data):
    print(f"{i}: {node.name} on {[q._index for q in node.qargs]}")

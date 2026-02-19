import matplotlib.pyplot as plt
from qiskit.converters import circuit_to_dag
from dag import show_dag
from qiskit import QuantumCircuit

qc = QuantumCircuit(2)
qc.x(0)

qc.h(1)

qc.cx(0, 1)

qc.x(0)
qc.z(1)

qc.draw('mpl')
plt.figure()
plt.show(block=False)


dag = circuit_to_dag(qc)
show_dag(dag)

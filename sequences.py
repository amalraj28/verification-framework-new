from qiskit import QuantumCircuit
from qiskit.circuit.library import HGate, XGate, YGate, ZGate, SGate, SdgGate, TGate, TdgGate


_SINGLE_QUBIT_GATE_MAP = {
    "h": HGate,
    "x": XGate,
    "y": YGate,
    "z": ZGate,
    "s": SGate,
    "sdg": SdgGate,
    "t": TGate,
    "tdg": TdgGate,
}


def get_single_qubit_ops(seq: list[str]):
    ops = []

    for name in seq:
        if name not in _SINGLE_QUBIT_GATE_MAP:
            raise ValueError(f"Unsupported single-qubit gate name: {name}")

        ops.append(_SINGLE_QUBIT_GATE_MAP[name])

    return ops


inverse_pairs = {
    "h": ["h", "h"],
    "t": ["t", "tdg"],
    "s": ["s", "sdg"],
    "tdg": ["tdg", "t"],
    "sdg": ["sdg", "s"],
    "x": ["x", "x"],
    "y": ["y", "y"],
    "z": ["z", "z"],
}


cloaked_gates_sequences = {
    "x": [
        ["h", "z", "h"],
        ["s", "y", "s", "z"],
        ["z", "sdg", "y", "sdg"],
        ["h", "y", "z", "h", "y"],
        ["y", "h", "z", "y", "h"],
        ["h", "y", "h","y", "sdg", "y", "s"],
        ["sdg", "y", "s", "h", "y", "h", "y"],
        ["s", "y", "sdg"],
    ],
    "y": [
        ["sdg", "x", "s"],
        ["sdg", "x", "z", "sdg"],
        ["s", "z", "x", "s"],
    ],
    "z": [
        ["h", "x", "h"],
        ["x", "s", "y", "s"],
        ["sdg", "y", "sdg", "x"],
        ["y", "h", "x", "y", "h"],
        ["h", "y", "x", "h", "y"],
        ["s", "s"],
        ["t", "t", "t", "t"],
    ],
    "s": [
        ["t", "t"],
        ["z", "t", "z", "t"],
        ["tdg", "tdg", "z"]
    ],
}


delayed_gates_sequences = {
    "x": [
        ["h", "z", "x", "h", "z"],
        ["h", "y", "h", "y", "z", "x", "z"],
        ["h", "y", "h", "x", "y"],
        ["y", "x", "h", "y", "h"],
        ["z", "h", "x", "z", "h"],
        ["z", "x", "z", "y", "h", "y", "h"],
    ],
    "y": [["x", "h", "y", "h", "x"]],
    "z": [
        ["h", "y", "h", "z", "y"],
        ["y", "z", "h", "y", "h"],
        ["h", "y", "h", "y", "x", "z", "x"],
        ["x", "z", "x", "y", "h", "y", "h"],
        ["x", "h", "z", "x", "h"],
        ["h", "x", "z", "h", "x"],
        ["sdg", "z", "s"],
        ["s", "z", "sdg"],
    ],
    "h": [["x", "z", "h", "x", "z"], ["z", "x", "h", "z", "x"]],
    "s": [
        ["z", "t", "sdg", "t"],
        ["z", "tdg", "s", "t", "z"],
        ["h", "y", "h", "s", "x"],
    ],
    "t": [["z", "sdg", "t", "s", "z"], ["z", "s", "t", "sdg", "z"]],
}


def auxiliary_gate():
    sub_circuit = QuantumCircuit(1, name="auxiliary")
    sub_circuit.h(0)
    sub_circuit.h(0)
    sub_circuit.z(0)
    sub_circuit.x(0)
    sub_circuit.z(0)
    sub_circuit.x(0)
    auxiliary = sub_circuit.to_gate()
    auxiliary.name = "auxiliary"
    return auxiliary


def restore_gate():
    sub_circuit = QuantumCircuit(1, name="restore")
    sub_circuit.x(0)
    sub_circuit.z(0)
    sub_circuit.x(0)
    sub_circuit.z(0)
    sub_circuit.h(0)
    sub_circuit.h(0)
    restore = sub_circuit.to_gate()
    restore.name = "restore"
    return restore

compositeGateSequences = {"aux": auxiliary_gate(), "res": restore_gate()}

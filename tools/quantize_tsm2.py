#!/usr/bin/env python3
"""Quantize a CUDA TSM2 model into deterministic TSM3 int8 weights."""

import argparse
import struct


def quantize(values):
    maximum = max((abs(value) for value in values), default=0.0)
    scale = maximum / 127.0 if maximum else 1.0
    result = [max(-127, min(127, int(round(value / scale)))) for value in values]
    return result, scale


def q16(value):
    return max(-2147483648, min(2147483647, int(round(value * 65536.0))))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    args = parser.parse_args()
    with open(args.input, "rb") as source:
        if source.read(4) != b"TSM2":
            raise SystemExit("expected TSM2 model")
        version, feature_dim, hidden_dim, action_count = struct.unpack("<4I", source.read(16))
        if version != 1:
            raise SystemExit("unsupported TSM2 version")
        w1 = list(struct.unpack(f"<{feature_dim * hidden_dim}f", source.read(feature_dim * hidden_dim * 4)))
        b1 = list(struct.unpack(f"<{hidden_dim}f", source.read(hidden_dim * 4)))
        value = list(struct.unpack(f"<{hidden_dim}f", source.read(hidden_dim * 4)))
        value_bias = struct.unpack("<f", source.read(4))[0]
        policy = list(struct.unpack(f"<{action_count * hidden_dim}f", source.read(action_count * hidden_dim * 4)))
    q_w1, w1_scale = quantize(w1)
    q_value, value_scale = quantize(value)
    q_policy, policy_scale = quantize(policy)
    q_b1 = [int(round(value / w1_scale)) for value in b1]
    with open(args.output, "wb") as destination:
        destination.write(b"TSM3")
        destination.write(struct.pack("<4I", 1, feature_dim, hidden_dim, action_count))
        destination.write(struct.pack("<4i", q16(1.0), q16(w1_scale), q16(policy_scale), q16(value_scale)))
        destination.write(struct.pack(f"<{len(q_w1)}b", *q_w1))
        destination.write(struct.pack(f"<{len(q_b1)}i", *q_b1))
        destination.write(struct.pack(f"<{len(q_value)}b", *q_value))
        destination.write(struct.pack("<i", int(round(value_bias / value_scale))))
        destination.write(struct.pack(f"<{len(q_policy)}b", *q_policy))
    print(f"quantized feature_dim={feature_dim} hidden_dim={hidden_dim} actions={action_count}")


if __name__ == "__main__":
    main()

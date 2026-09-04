#!/usr/bin/env python3
"""Non-rigorous independent diagnostics for the strengthened-curvature note.

These checks are not part of the proof certificate.  They are included to make
it easy to detect transcription or implementation mistakes independently of
the interval verifier.
"""
from __future__ import annotations
import math
import random
from pathlib import Path
import numpy as np
import mpmath as mp

random.seed(20260829)
np.random.seed(20260829)

# Load only definitions from the certified verifier (do not execute its queue).
path = Path(__file__).with_name("verify_0715579_strengthened_curvature_revised.py")
text = path.read_text()
ns = {}
exec(text.split("\nD_SUB = 10")[0], ns)
RAW = ns["RAW"]
f_best_lambda = ns["f_best_lambda"]
f_eval = ns["f_eval"]


def schedule(d: float):
    for i in range(len(RAW) - 1):
        d0 = RAW[i][0] / 1000
        d1 = RAW[i + 1][0] / 1000
        if d <= d1 + 1e-15:
            w = (d - d0) / (d1 - d0)
            a = (RAW[i][1] + w * (RAW[i + 1][1] - RAW[i][1])) / 1e9
            b = (RAW[i][2] + w * (RAW[i + 1][2] - RAW[i][2])) / 1e9
            return a, b
    return RAW[-1][1] / 1e9, RAW[-1][2] / 1e9


# 1. Random exact-identity/sign-imbalance checks.
max_identity_error = 0.0
min_imbalance_slack = float("inf")
min_curvature_slack = float("inf")
for _ in range(500):
    n = np.random.randint(1, 7)
    m = np.random.randint(n + 1, n + 12)
    A = np.random.randn(m, n)
    H = A.T @ A
    ew, EV = np.linalg.eigh(H)
    U = A @ (EV @ np.diag(1 / np.sqrt(ew)) @ EV.T)
    c = np.random.randn(n)
    c /= np.linalg.norm(c)
    alpha = U @ c
    t = 10 ** np.random.uniform(-1, 1)
    s = np.random.uniform(-0.75, 0.75)
    if np.min(1 + s * alpha) <= 0:
        continue
    rows = U / (1 + s * alpha)[:, None]
    Vrows = np.vstack([c[None, :] / t, rows])
    M = Vrows.T @ Vrows
    P = Vrows @ np.linalg.inv(M) @ Vrows.T
    D = np.diag(np.r_[0.0, alpha / (1 + s * alpha)])
    Q = np.eye(m + 1) - P
    fpp_a = 6 * np.trace(P @ D @ D) - 4 * np.trace(P @ D @ P @ D)
    T = np.linalg.norm(P @ D @ P, "fro") ** 2
    W = np.linalg.norm(Q @ D @ Q, "fro") ** 2
    fpp_b = 3 * np.linalg.norm(D, "fro") ** 2 - T - 3 * W
    d = np.diag(D)
    p = np.linalg.norm(d[d > 0])
    q = np.linalg.norm(d[d < 0])
    max_identity_error = max(max_identity_error, abs(fpp_a - fpp_b))
    min_imbalance_slack = min(min_imbalance_slack, T + W - 0.5 * (p - q) ** 2)
    min_curvature_slack = min(
        min_curvature_slack,
        3 * np.linalg.norm(D, "fro") ** 2 - 0.5 * (p - q) ** 2 - fpp_a,
    )


# 2. Closed-form cross-over integral versus independent quadrature.
def cross_formula(length, P, N):
    if P <= N:
        return 0.0
    if N < 1e-14:
        U = 1 + P * length
        return 0.5 * ((P * length + 1) * (1 - 1 / U) - math.log(U))
    s0 = (P - N) / (2 * P * N)
    L = min(length, s0)
    if L <= 0:
        return 0.0
    U = 1 + P * L
    V = 1 - N * L
    t1 = (P * length + 1) * (1 - 1 / U) - math.log(U)
    t2 = (N * length - 1) * (1 / V - 1) - math.log(V)
    J1 = ((P * length + 1) * math.log(U) - (U - 1)) / (P * P)
    J2 = (-(N * length - 1) * math.log(V) + (1 - V)) / (N * N)
    I3 = P / (P + N) * J1 + N / (P + N) * J2
    return 0.5 * (t1 + t2 - 2 * P * N * I3)

max_cross_error = 0.0
mp.mp.dps = 70
for _ in range(50):
    r = random.uniform(0.5001, 0.9999)
    P = math.sqrt(r)
    N = math.sqrt(1 - r)
    length = random.uniform(0.01, 0.9)
    L = min(length, (P - N) / (2 * P * N))
    integrand = lambda x: 0.5 * (length - x) * (
        P / (1 + P * x) - N / (1 - N * x)
    ) ** 2
    quad = float(mp.quad(integrand, [0, L]))
    max_cross_error = max(max_cross_error, abs(cross_formula(length, P, N) - quad))


# 3. Dense, non-rigorous scan of the final scalar envelope.
max_envelope = -float("inf")
max_location = None
for d in np.linspace(0, 0.411, 207):
    a, b = schedule(float(d))
    for r in np.linspace(0, 1, 501):
        lam = f_best_lambda(float(d), a, b, float(r))
        value = f_eval(float(d), a, b, float(r), lam)
        if value > max_envelope:
            max_envelope = value
            max_location = (float(d), float(r), a, b, lam)

print("DIAGNOSTIC PASS")
print("max F'' identity error", max_identity_error)
print("minimum sign-imbalance slack", min_imbalance_slack)
print("minimum strengthened-curvature slack", min_curvature_slack)
print("max cross-formula/quadrature error", max_cross_error)
print("dense-grid max log envelope", max_envelope)
print("dense-grid max determinant envelope", math.exp(max_envelope))
print("dense-grid location", max_location)
print("target log", math.log(6.94))

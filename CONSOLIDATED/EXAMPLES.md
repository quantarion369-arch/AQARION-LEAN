# AQARION Lean — Worked Examples

## Restricted-growth strings

For a three-element set, the five set partitions are:

1. [[0,1,2]]
2. [[0,1],[2]]
3. [[0,2],[1]]
4. [[0],[1,2]]
5. [[0],[1]]

Thus:

    partitions 3 = 5

## Weighted Bell anchors

The recorded finite anchors are:

    weightedBell [1,1,2] = 7
    weightedBell [2,2] = 7
    weightedBell [2,2,2] = 31
    weightedBell [2,4] = 9
    weightedBell [3,3] = 8

These check specific inputs. They do not prove a universal weighted-Bell theorem by themselves.

## Gate 2 mutation example

The original calculation uses a greatest-common-divisor style block weight.

For the input [2,4]:

    listGcd [2,4] = 2

The mutation replaces this with a least-common-multiple calculation:

    lcm [2,4] = 4

Because the block weight changes, the affected weighted-Bell anchor fails. This demonstrates that Gate 2 detects the tested semantic mutation.

## PB-CORE-006 EGF correction

The incorrect expression was:

    sum A_n/n! z^n = P(T(z)) - 1

The corrected expression is:

    sum A_n/n! z^n = P(T(z))

where:

    P(z) = sum p(k) z^k
    T(z) = z e^(T(z))

The correction is required because the left-hand side and P(T(z)) both have constant term zero, while P(T(z)) - 1 has constant term negative one.

This corrects the generating-function form. It does not yet prove that the intended PBCore006 sequence equals the coefficients of P(T(z)).

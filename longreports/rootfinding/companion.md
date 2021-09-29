# Rootfinding by sticking the [companion](https://en.wikipedia.org/wiki/Companion_matrix) matrix into an eigenvalue solver

For every `n` in `nat`, forall `p` in the real polynomials of degree `n` arranged such that the leading coefficient is `1`, the **companion matrix** of `p` is an `n x n` matrix. It's characteristic polynomial happens to be `p`. 

```haskell
-- n is the number of assets on the balance sheet.
-- a and b are coefficients in terms of balance sheet and amplification coefficient,
-- -- here for details of a and b https://github.com/ArdanaLabs/audit/blob/main/newton-robustness.ipynb
companion :: Int -> Double -> Double -> [[Double]]
companion n a b = [
  (take n $ repeat 0) ++ [- b],
  [1] ++ (take (n - 1) $ repeat 0) ++ [- a]
  ] 
  ++ 
  (tail $ take n $ identity (n + 1))
```

## LAPACK

There exists [a haskell wrapper around lapack](https://hackage.haskell.org/package/lapack)

Morgan provided a breakdown of considerations comparing the lapack wrapper's eigensolver with our own newton's method implementation.

Here are some things to consider in considering using any algorithm implementation (first party or third party) to solve the invariant equation.

### 1. That algorithm will have limited precision and conditions for finding accurate solutions to our particular problems. Are those conditions met by the current invariant problem? Will they be met by future invariant problems?

**LAPACK**:
- [Here is a page about the precision of its eigenvalue solver](https://www.netlib.org/lapack/lug/node91.html)
- Margin of error is 3.1e-1

What about accuracy? Is the solver guaranteed to be accurate? What is the algorithm for the approximation? What are the assumptions of this algorithm? I don't know the answers to these questions.

**Newton**: 
- Conditions for precision and accuracy are not exactly known.
- We could learn more in simulations

### 2. What platforms support that algorithm implementation?

- **LAPACK**: Haskell but not Plutus
- **Newton**: Haskell and Plutus

### 3. What platforms do we need the algorithm implementation to run on?

- Just Haskell, just on our own machines

### 4. Who supports the implementation and what kind of support is available to us?

**LAPACK**: actively [maintained on GitHub with 72 contributors and 2,295 commits](https://github.com/Reference-LAPACK/lapack); issues on GitHub have about 50% rate of engagement; unknown what support is available

**Haskell LAPACK**: actively maintained by [Dr. Henning Thielemann](http://henning-thielemann.de/); unknown what level of support is available

**Newton**: it's all on us

### 5. How has the implementation been tested?

**LAPACK**: has half a million lines of test code

**Haskell LAPACK**: has 7.5k lines of unit tests

**Newton**: it's all on us and the testing is currently not sufficient

### 6. What is the performance like on expected problem sizes?

**LAPACK**: unknown

**Newton**: unknown, but sufficient, based on property tests

## `Eigen`

`Eigen` is a C++ library that is widely trusted. There exists a wrapper for haskell. 

I think I can figure out how to recover eigenvalues from [`matrixQ` and `matrixR` here](https://hackage.haskell.org/package/eigen-3.3.7.0/docs/Eigen-Solver-SparseLA.html)

## Home rolled eigensolver

[This book](https://www.cs.cornell.edu/cv/GVL4/golubandvanloan.htm) comes very highly recommended to me by someone I trust a lot. Page 347-426 is chapter 7 on unsymmetric eigenvalue problems. 

Here's a pile of wikipedia pages
- [Inverse iteration](https://en.wikipedia.org/wiki/Inverse_iteration)
- [Jenkins-Traub](https://en.wikipedia.org/wiki/Jenkins%E2%80%93Traub_algorithm)
- [QR algorithm](https://en.m.wikipedia.org/wiki/QR_algorithm)

### The case against

> If I were an attacker I'd want people doing as much custom code as possible, because I'm better at it than them, but I'm not better at it than the library authors. (a friend of mine)

Standard engineer wisdom is not to roll your own, because a distributed community can find bugs more adequately than your team. 

### The case for 

General purpose algorithms are frequently less than 100% accurate on specific problems. Less than 100% is ok for a lot of scientific applications, but not for defi. 


# Rootfinding for the invariant polynomials

Per stableswap, we need to solve an _invariant equation_, once for the parameter `D` and once for every `x_k` in the balance sheet. 

I transformed the invariant _equation_ into an invariant _polynomial_, in one form when `D` is the unknown of interest and another form whan an `x_k` is the unknown of interest, details in [newton robustness notebook](/newton-robustness.ipynb). 

Now that we have polynomials `p`, we want to find the `x` such that `p(x) = 0` for each `p` we have. Hence, the task is _rootfinding_. 

## Some notes

- [Brent's method](https://en.wikipedia.org/wiki/Brent%27s_method) (aspects of bisection and newton)


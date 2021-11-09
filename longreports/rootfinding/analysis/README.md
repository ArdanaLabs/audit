# Analytics of rootfinding method

Please upload new `csv`s in in `/data/` 

## To reproduce
```bash
nix-shell lab.nix --run "jupyter lab"
``` 

## Just kidding, I can't get `numpyro` in a `.nix` build with `jupyter lab` and I can't get vice versa either. So docker it is.

``` bash
docker build -t data-analysis-ppl:conda ..
docker run -it -p 8888:8888 -v $(pwd):/home/ data-analysis-ppl:conda jupyter lab --allow-root --ip=0.0.0.0
```

from functools import partial
import pandas as pd
import altair
import scipy
import jax
import arviz
import matplotlib

from eda import _heatmap_, _heatmaps_, _mkscatter_, _mkkde_

def tofloat(dat: pd.DataFrame) -> pd.DataFrame:
    """Convert pretty printed rationals to floats."""
    return dat.assign(**{col: dat[col].map(eval) for col in dat.columns})

def mknewtondelta(dat: pd.DataFrame, abso: bool) -> pd.DataFrame:
    diff = dat.D - dat.Root
    if abso:
        newton_delta = diff.abs()
    else:
        newton_delta = diff
    """How far does newton take the initial guess to the final guess?"""
    return dat.assign(newton_delta=newton_delta)

def sqnewtondelta(dat: pd.DataFrame) -> pd.DataFrame:
    return dat.assign(squared_newton_delta=dat.newton_delta ** 2)

def clean(dat: pd.DataFrame, abso: bool) -> pd.DataFrame:
    return dat.pipe(tofloat).pipe(mknewtondelta, abso).pipe(sqnewtondelta)

class Clean:
    def __init__(self, filepath: str, *, abso: bool = True):
        self.filepath = filepath
        self.abso = abso
        self._df = pd.read_csv(filepath, header=1)
        self.df = clean(self._df, abso)
        self._heatmap = partial(_heatmap_, scipy.stats, altair, self.df)
        self._heatmaps = partial(_heatmaps_, scipy.stats, altair, self.df)
        self._mkscatter = partial(_mkscatter_, jax.numpy, matplotlib.pyplot, self.df)
        self._mkkde = partial(_mkkde_, arviz, self.df)

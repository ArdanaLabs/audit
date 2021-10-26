from functools import reduce

def _mkscatter_(jnp: "module", plt: "module", df: "pd.DataFrame", col: str) -> "IO(plt.axis)":
    assert col in df.columns, "col must be in df.columns"
    col_df = df[col]
    plt.scatter(
        jnp.linspace(start=col_df.min(), stop=col_df.max(), num=col_df.size),
        col_df,
        alpha=0.2,
    )
    plt.title(col);

def _mkkde_(az: "module", df: "pd.DataFrame", col: str) -> "IO(plt.Axis)":
    az.plot_kde(df[col]);


def _heatmap_(stats: "module", alt: "module", dat: "pd.DataFrame", x: str, y: str, color: str) -> "alt.Chart":
    return (
        alt.Chart(dat[(abs(stats.zscore(dat[color])) < 3)].sample(4999))
        .mark_rect()
        .encode(
            x=alt.X(f"{x}:O", bin=alt.BinParams(maxbins=100)),
            y=alt.Y(f"{y}:O", bin=alt.BinParams(maxbins=100)),
            color=f"{color}:Q"
        )
        .properties(width=500, height=500)
    )

def _heatmaps_(stats: "module", alt: "module", dat: "pd.DataFrame", axis: str) -> "alt.Chart":
    """Returns a horizontal array of heatmaps, also drops outliers from dat[axis]"""
    assert axis in dat.columns, f"Given axis {axis} not in dat.columns"
    return reduce(
        lambda C,D: C | D,
        (heatmap(stats, alt, dat.sample(4999), x, y, axis)
        for x,y
        in combinations((
            col for col in dat.columns if col != axis
        ), 2))
    )

def intslider_wrap(intslider: "widgets.IntSlider", dat: "pd.DataFrame") -> "widgets.IntSlider":
    return intslider(min=0, max=dat.shape[1] - 1, step=1, value=0)

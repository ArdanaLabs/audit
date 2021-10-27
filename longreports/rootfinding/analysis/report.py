from clean import Clean

class Report(Clean):
    def __init__(self, filepath: str, *, unknown_feature: str, abso: bool = False):
        super().__init__(filepath, unknown_feature=unknown_feature, abso=abso)

    def negative_solutions(self) -> float:
        return self.df[self.df.Root < 0].shape[0] / self.df.shape[0]

    def report_negative_solutions(self) -> str:
        return f"Solver gave a negative root {100 * self.negative_solutions():.4}% of the time"

import mltl_simplification as simp


def main():
    formula = simp.Formula("(G l1 & b1 -> s1) & (G l2 & b2 -> s2)")
    knowledge = simp.KnowledgeSequence({
        0: (["l2", "b2"], ["b1"], [], []),
        1: ([], [], [("b1", "b2"), ("s1", "s2")], [("l1", "l2")]),
    })
    augmenter = simp.Augmenter(knowledge)
    augmented = augmenter.augment(formula)
    print(augmented)


if __name__ == "__main__":
    main()

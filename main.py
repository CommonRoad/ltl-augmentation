import ltl_augmentation as aug


def main():
    formula = aug.Formula("(G l1 & b1 -> s1) & (G l2 & b2 -> s2)")
    print(f"Original formula:\n{formula}")
    knowledge = aug.KnowledgeSequence(
        {
            0: (["l2", "b2"], ["b1"], [], []),
            1: ([], [], [("b1", "b2"), ("s1", "s2")], [("l1", "l2")]),
        }
    )
    augmenter = aug.Augmenter(knowledge)
    augmented = augmenter.augment(formula)
    print(f"Augmented formula:\n{augmented}")


if __name__ == "__main__":
    main()

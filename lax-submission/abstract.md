We study black-peg permutation Mastermind when each round supplies the usual
number of exact matches together with one additional Boolean answer.  The
Boolean check may be selected adaptively after the black-peg count is known.

The submission formalizes the information-theoretic decision-tree argument:
with `n!` permutation secrets and at most `2(n+1)` answers per round, every
solving deterministic strategy of depth `r` induces an injection into a
transcript space of cardinality `(2(n+1))^r`.  We also prove the specialization
to ten fields and eleven colors, where there are `11! = 39,916,800` injective
secrets and consequently at least six rounds are necessary.

The surrounding repository develops a stronger structural lower bound of eight
rounds and a mathematical upper-bound protocol.  Those stronger results are
kept separate from the two closed, assumption-free conclusions archived here.

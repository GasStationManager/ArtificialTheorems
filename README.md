# ArtificialTheorems: Autoformalization of Theoretical Foundations of AI/ML

This repo is a library of Lean formalizations of theoretical foundations of AI and ML. We explicitly allow and encourage AI-generated / AI-assisted proofs, with the following quality assurance:
- The formal theorem statements (in directory `ArtificialTheoremsSpec/`) are vetted by human experts.
- The proofs (in `ArtificialTheorems/`) are checked using secure verifiers (Comparator, SafeVerify) to ensure that they prove exactly the statements in `ArtificalTheoremsSpec/`


## Wish List

Contributions are appreciated! Both formal theorem statements vetted by human experts, and autoformalizations of proofs. 
I am particularly interested in these areas:

- Universal representation theorems for deep neural nets
- Generalization theory
  - A recent Lean formalization of generalization error bound by Radmacher complexity: https://github.com/auto-res/lean-rademacher  
- Implicit regularization (how training via SGD can achieve generalization)
- RL theory
  - A recent Lean formalization of convergence of Q-Learning: https://github.com/ShangtongZhang/rl-theory-in-lean
- Bayesian learning; and perhaps building on top of that, Singular Learning Theory.

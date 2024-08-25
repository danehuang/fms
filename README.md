# Formal Models and Semantics

## References

This course would not be possible without these amazing resources.
- [https://softwarefoundations.cis.upenn.edu/](https://softwarefoundations.cis.upenn.edu/)
- [https://github.com/coq-community/reglang](https://github.com/coq-community/reglang)
- [https://github.com/fakusb/coq-library-undecidability/tree/7033c536b9d9a89214c57082dcf20f00002f48d2](https://github.com/fakusb/coq-library-undecidability/tree/7033c536b9d9a89214c57082dcf20f00002f48d2)

Lecture notes draw heavily from these resources.

The web verion is here [https://danehuang.github.io/fms/](https://danehuang.github.io/fms/).


## Syllabus

- Lectures 1-4 give introduction to proofs and mechanization in Coq based off of Software foundations.
- Lectures 5-7 formalize abstract machines in Coq (DFA and TM).
- Lectures 8-9 formalize IMP (imperative language) and axiomatic-semantics via Hoare logic based off of Software foundations.
- Lectures 10-12 formalize Lambda Calculus, Simply-Typed Lambda Calculus (STLC), and Type-checking/Type Inference partially based off of Software foundations.
- Lecture 13 goes over a proof of strong normalization of STLC via logical relations based off of Software foundations.


## Compiling

1. We use Coq Version 8.12.2
2. Build all lectures `./build.sh`
    - `./build_cooklevin.sh` is needed for the lectures on Turing machines. This can take a while.

### More compilation

- You should be able to run `coqc` on any lecture / file that is necessary.
- The lectures on DFAs/REs require `lib_reglang.v` (based off of [https://github.com/coq-community/reglang](https://github.com/coq-community/reglang))
- The lecture on Turing machines require [https://github.com/fakusb/coq-library-undecidability/tree/7033c536b9d9a89214c57082dcf20f00002f48d2](https://github.com/fakusb/coq-library-undecidability/tree/7033c536b9d9a89214c57082dcf20f00002f48d2)

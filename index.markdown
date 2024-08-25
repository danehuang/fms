---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

layout: home
---

A series of notes on formal models and semantics. 

These notes would not be possible without these amazing resources.
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [Regular Languages](https://github.com/coq-community/reglang)
- [Coq Library on Undecidability](https://github.com/fakusb/coq-library-undecidability/tree/7033c536b9d9a89214c57082dcf20f00002f48d2)

The notes draw heavily from these resources.

## Content

- Lectures 1-4 give introduction to proofs and mechanization in Coq based off of [Software Foundations](https://softwarefoundations.cis.upenn.edu/).
- Lectures 5-7 formalize abstract machines in Coq (DFA and TM) based off of [Regular Languages](https://github.com/coq-community/reglang) and [Coq Library on Undecidability](https://github.com/fakusb/coq-library-undecidability/tree/7033c536b9d9a89214c57082dcf20f00002f48d2).
- Lectures 8-9 formalize IMP (imperative language) and axiomatic-semantics via Hoare logic based off of [Software Foundations](https://softwarefoundations.cis.upenn.edu/).
- Lectures 10-12 formalize Lambda Calculus, Simply-Typed Lambda Calculus (STLC), and Type-checking/Type Inference partially based off of [Software Foundations](https://softwarefoundations.cis.upenn.edu/).
- Lecture 13 goes over a proof of strong normalization of STLC via logical relations based off of [Software Foundations](https://softwarefoundations.cis.upenn.edu/).

## Notes

<ul>
  {% for page in site.pages %}
    <li>
      <a href="{{ site.baseurl }}{{ page.url }}">{{ page.title }}</a>
    </li>
  {% endfor %}
</ul>
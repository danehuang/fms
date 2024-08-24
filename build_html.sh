#! /bin/bash

coqdoc lec_01_intro.v --parse-comments
coqdoc lec_02_fp.v --parse-comments
coqdoc lec_03_proof.v --parse-comments
coqdoc lec_04_rel.v --parse-comments
coqdoc lec_05_dfa.v --parse-comments
coqdoc lec_06_re.v --parse-comments
coqdoc lec_07_tm.v --parse-comments
coqdoc lec_08_imp.v --parse-comments
coqdoc lec_09_hl.v --parse-comments
coqdoc lec_10_lambda.v --parse-comments
coqdoc lec_11_stlc.v --parse-comments
coqdoc lec_12_infer.v --parse-comments
coqdoc lec_13_norm.v --parse-comments

mv *.html _includes
mv coqdoc.css _includes

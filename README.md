## Formalizing AI Reliability in Lean 4
This repository contains Lean 4 formalizations of two theorems relevant to the epistemology of artificial intelligence. It is in conversation with Eamon Duede's paper "Instruments, Agents, and Artificial Intelligence: Novel Epistemic Categories of Reliability" (Synthese, 2022).

# Overview
Duede argues that the reliability of Deep Learning agents (DL) cannot be justified by reducing them to either scientific instruments or expert agents. 
This repository formalizes two key concepts that support this argument:

* NFL.lean – No Free Lunch (NFL) demonstrates why past performance cannot justify future reliability without assumptions about problem structure.
* ER.lean – The Experimenter's Regress (ER) formalizes Henry Collins's insight about circular dependence in evaluating experimental validity, and extends it to AI systems
  
Both formalizations are self-contained, fully type-checked, and extensively commented for pedagogical purposes.

## Kevins TOODs
1. Unification Funktion in den Context speichern

## Tasks

1. Thesis writing
2. Hint Unification Example #2 (Reification)
3. Modularisieren
  - First_Steps killen (Tests nach HO tests) #DONE
  - alle unifier werden eine Instanz aus der generischen Funktion, die eine try_hints Funktion und Pattern matcher als Parameter erwartet #DONE
4. Beispiel, warum lineare Ordnung der Praemissen wichtig ist #DONE

10. Named theorems: Reihenfolge umdrehen
7. Taktik erstellen
9. Stepwise hints anwenden und mit user kommunizieren

## Writing

1. Introduction
    - Motivation
    - Outline
2. Preliminaries
    - Lambda Calculus with simple types
    - Unification
3. Unification Hints
4. Implementation
    - HO-Pattern Matcher 
    - Pure
    - Was denkst du, muss derjenige, der es gerne erweitern will, wissen?
    - Debugging
5. Applications
  - simple examples with recursion
  - simple reification
  - more complex reification possible (cf paper)
  - canonical instances
  - typeclasses
  - pullbacks
  - non-uniform coercions
6. Future & Related Work
    - What's missing?

2.3 Isabelle: user experience aktuell ==> motivation fuer unification hints 
3. Type classes beispiel. Reification auf Chapter 5 verweisen. Non-uniform coercions paper zitieren
4.1 Hint Unif. Function with Parameters (both 
unifier functions); dann first-order unifier (Beispiele), dann first-order mit HO matcher fuer hints (Beispiele); dann higher-order pattern matcher (Beispiele); TODO future: higher-order full unification
4.1 Theorem Sequenze in Zukunft waere besser
4.2. Explain why pattern matcher;
4. Theorem bauen; Komplikationen falls es welche gab oder wenn nicht, warum es einfach war;
4. Theoreme zusammenbauen (rechts nach links da goals von links nach rechts geloest werden)
4.2 Highlight that bound variables do not have an associated type and current implementation does not work in those cases
4.3 Execution Traces
  - Reihenfolge Beispiel wichtig
5. Simple examples for unification problems (tagging, calling the function)
5.1 Simple reification example
6. Related Work: Implementierungen. zb Matita, Coq, ...

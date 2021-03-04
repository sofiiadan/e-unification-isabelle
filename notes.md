## TODOs (Kevin)
- Fragen, ob man die unification Funktion in den Context speichern soll
- declare mit Variables aus ML

## Tasks

1. Rekursive Strategie mit Backtracking:
    - Offensichtliche Probleme
    - Beispiele, wo es ein Problem gibt
    - Implementierungsueberlegungen
7. Wie kann man Funktionen, die eine Liste von Moeglichkeiten erzeugen, in eine Taktik auslagern
8. Statt index eine Funktion mitreichen in den Taktiken
  - Kevin fragt zuerst, ob wir das so machen sollen
9. Stepwise hints anwenden und mit user kommunizieren
10. Named theorems: Reihenfolge umdrehen
11. Wo koennte man Unification brauchen? -> …


## Tests

#DONE

1. Symmetrie
2. 2. Environment unverändert bei identischen Termen
3. Ergebnisenvironment-Korrektheit: t1\sigma = t2\sigma
4. 4.Ergebnistheorem-Korrektheit
    Nicht-unifizierbare Terme:
    Occurs-Check
    Var-freie, ungleiche Terme
    Unifizierbare Terme:
    Identische Terme
    Var/beliebiger Term
    Term t mit t allen Vars durch Frees ersetzt
    Explizite Tests mit Var vs Free und TVar vs TFree
    Explizite Tests mit verschiedenen Free/TFree-Symbolen, die nicht unifizieren
    Tests, die zunaechst failen, dann hint hinzufuegen und dann klappen
    Tests mit mehreren anwendbaren hints, aber nur einer fuehrt zum Erfolg (auch wenn der hint frueher hinzugefuegt)


# TODO Tests mit rekursiver Unification
1. unification hints
  - Prämissenordnung = Lösungsordnung testen
2. Rekursiv Hints anwenden
3. Tests mit rekursiven Hints
  - Mehrere Hints notwendig, um zu unifizieren.

## Done
1. Idx anpassen mit `Thm.incr_indexes`
2. Refaktoring, modulare Funktionen
3. Reflection proofs dischargen
4. Eta contraction beim Einfuegen und bei Aufruf zweier Terme
5. Pattern Matching -> Unification passt fuer den First-order unifier von Paul
6. Eta contraction beim Einfuegen
7. Validitaetscheck: Kernel unifier funktioniert auch
8. Testframework angeschaut
9. Basic Logger bauen

## Features for the Future
- Termindexing fuer die Hints

## Themennamen
- Unifikation Höherer Ordnung mit Hinweisen in Isabelle
- Higher-Order Unification with Hints in Isabelle

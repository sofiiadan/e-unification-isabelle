## Kevins TOODs
1. Unification Funktion in den Context speichern

## Tasks

1. Hint Unification Example #2 (Reification)
2. Beispiel, warum lineare Ordnung der Praemissen wichtig ist
Future:
1. Named theorems: Reihenfolge umdrehen
2. Taktik erstellen
3. Stepwise hints anwenden und mit user kommunizieren

## Tests done

- Symmetrie
- Environment unverändert bei identischen Termen
- Ergebnisenvironment-Korrektheit: t1\sigma = t2\sigma
- Ergebnistheorem-Korrektheit
- Nicht-unifizierbare Terme:
- Occurs-Check
- Var-freie, ungleiche Terme
- Unifizierbare Terme:
- Identische Terme
- Var/beliebiger Term
- Term t mit t allen Vars durch Frees ersetzt
- Explizite Tests mit Var vs Free und TVar vs TFree
- Explizite Tests mit verschiedenen Free/TFree-Symbolen, die nicht unifizieren
- Tests, die zunaechst failen, dann hint hinzufuegen und dann klappen
- Tests mit mehreren anwendbaren hints, aber nur einer fuehrt zum Erfolg (auch wenn der hint frueher hinzugefuegt)

## TODO Tests
4. unification hints
  - Prämissenordnung = Lösungsordnung testen
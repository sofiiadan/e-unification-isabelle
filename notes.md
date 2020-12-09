# Notes 

- try_hint: idxs von term1,term2 erhöhen statt von hint: 
	Grund: idxs in hint_thm sind schwierig zu erhöhen
	Problem: dann müssen bei jedem try_hint alle idxs im envir erhöht werden
	Alternative: alle Frees aus thm sammeln, indizes in liste erhöhen und dann infer_intantiate
	
- try_hint_unif(_kernel): first order unification/kernel unification statt matching beim Abgleichen eines Hints.
	Ergebnis: funktioniert. Instanzierungen in einigen hint-thms müssen außerdem nicht mehr explizit in den prems angegeben werden, da sie sich durch unification ergeben.


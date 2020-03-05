# Explanations-by-contraint-decomposition
Institut Mines-Télécom - Master 2 ORO - Année 2020.
 * Stagiaire : 
    - Arthur GONTIER
 * Encadrants :
    - Charlotte TRUCHET
    - Charles PRUDHOMME
    
* Lien vers le suivit/rapport [overleaf](https://fr.overleaf.com/4384554372hfpvtcwvvvtc)  

Le but de ce stage est, lors de la résolution d'un problème de contrainte globale, 
de générer l'explication d'un évenement automatiquement à partir d'une décomposition de la dite contrainte globale.

Les fichiers moulinette.jl et moulinette2.jl sont des prototypes julia qui respectivement donne l'explication sur une instance de la contrainte cumulative à partir de sa décomposition et génère l'explication d'une contrainte à partir de sa décomposition seule.(note : les prototypes ne prennent pas en comptes tous les cas de décompositions)

Le fichier moulinette.ml est ce qui sera la vertion définitive du générateur d'explication.

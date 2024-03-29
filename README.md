# Explanations-by-constraint-decomposition
Institut Mines-Télécom - Master 2 ORO - Année 2020.
 * Stagiaire : 
    - Arthur GONTIER
 * Encadrants :
    - Charlotte TRUCHET
    - Charles PRUDHOMME
    
* Lien vers le suivit/rapport [overleaf](https://www.overleaf.com/8957513332vfpwstrxmhtj)  

[FR]

Le but de ce stage est de générer l'explication d'une contrainte globale à partir d'une de ses décomposition. Lors de la résolution d'un problème de contrainte globale, cette formule pourras être utilisée pour expliquer un évènement.

Le générateur d'explication est capable de générer une explication en Latex depuis une décomposition et un évènement quelconques. Et une version qui génère des explications pour le solveur CHOCO est en développement.

Pour les prototypes : Les fichiers moulinette.jl et moulinette2.jl sont des prototypes julia. Le premier donne l'explication d'un évènement sur une instance de la contrainte cumulative à partir de sa décomposition et le deuxième génère l'explication de n'importe quelle contrainte à partir de sa décomposition. (note : les prototypes ne prennent pas en comptes tous les cas de décompositions)
Le dernier prototype en ocaml structure le deuxième prototype julia.

[EN]

The goal of this internship is to generate the explanation formula of a constraint from it's decompositions. This formula can then be used to explain any event during the resolution of a global constraint problem. 

The explanation generator is capable of generating a Latex explanation from any decomposition and event. And the generation of CHOCO explanations is in developpement.

The moulinette.jl and moulinette2.jl files are julia prototypes. The first one give the explanation of an event on an instance of the cumulative constraint from its decomposition. The second one give the explanation of any constraint from its decomposition alone. (Note: the prototypes does not take into account all cases of decomposition)
The last Ocaml prototype structure the second julia prototype.

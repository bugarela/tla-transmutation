---------------------------- MODULE JarrosDeAgua ----------------------------
EXTENDS Integers

VARIABLES jarro_pequeno, jarro_grande   
         
(* TypeOK == /\ jarro_pequeno \in 0..3  *)
(*           /\ jarro_grande  \in 0..5 *)
          
Init == /\ jarro_grande   = 0
        /\ jarro_pequeno = 0
        
EnchePequeno == /\ jarro_pequeno' = 3
                /\ jarro_grande'  = jarro_grande
                
EncheGrande == /\ jarro_grande'  = 5
               /\ jarro_pequeno' = jarro_pequeno
               
EsvaziaPequeno == /\ jarro_pequeno' = 0
                  /\ jarro_grande'  = jarro_grande
                  
EsvaziaGrande == /\ jarro_grande'  = 0
                 /\ jarro_pequeno' = jarro_pequeno
                 
PequenoParaGrande == IF jarro_grande + jarro_pequeno =< 5
                     THEN /\ jarro_grande'  = jarro_grande + jarro_pequeno
                          /\ jarro_pequeno' = 0
                     ELSE /\ jarro_grande'  = 5
                          /\ jarro_pequeno' = jarro_pequeno - (5 - jarro_grande)
                          
GrandeParaPequeno == IF jarro_grande + jarro_pequeno =< 3
                     THEN /\ jarro_grande'  = 0
                          /\ jarro_pequeno' = jarro_grande + jarro_pequeno
                     ELSE /\ jarro_grande'  = jarro_pequeno - (3 - jarro_grande)
                          /\ jarro_pequeno' = 3

Inv == jarro_grande /= 4

Next == \/ EnchePequeno 
        \/ EncheGrande    
        \/ EsvaziaPequeno 
        \/ EsvaziaGrande    
        \/ PequenoParaGrande    
        \/ GrandeParaPequeno   
=============================================================================

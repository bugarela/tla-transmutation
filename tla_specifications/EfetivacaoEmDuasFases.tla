----------------------- MODULE EfetivacaoEmDuasFases -----------------------
CONSTANT GR 

VARIABLES estadoGR, estadoGT, GRsPreparados, msgs           

DFInit ==   
  /\ estadoGR = [g \in GR |-> "trabalhando"]
  /\ estadoGT = "inicio"
  /\ GRsPreparados   = {}
  /\ msgs = {}

GTRecebePrepara(g) ==
  /\ estadoGT = "inicio"
  /\ [tipo |-> "EstouPreparado", gr |-> g] \in msgs
  /\ GRsPreparados' = GRsPreparados \cup {g}
  /\ UNCHANGED <<estadoGR, estadoGT, msgs>>

GTEfetiva ==
  /\ estadoGT = "inicio"
  /\ GRsPreparados = GR
  /\ estadoGT' = "termino"
  /\ msgs' = msgs \cup {[tipo |-> "Efetive"]}
  /\ UNCHANGED <<estadoGR, GRsPreparados>>

GTAborta ==
  /\ estadoGT = "inicio"
  /\ estadoGT' = "termino"
  /\ msgs' = msgs \cup {[tipo |-> "Aborte"]}
  /\ UNCHANGED <<estadoGR, GRsPreparados>>

GRPrepara(g) == 
  /\ estadoGR[g] = "trabalhando"
  /\ estadoGR' = [estadoGR EXCEPT ![g] = "preparado"]
  /\ msgs' = msgs \cup {[tipo |-> "EstouPreparado", gr |-> g]}
  /\ UNCHANGED <<estadoGT, GRsPreparados>>
  
GREcolheAbortar(g) ==
  /\ estadoGR[g] = "trabalhando"
  /\ estadoGR' = [estadoGR EXCEPT ![g] = "abortado"]
  /\ UNCHANGED <<estadoGT, GRsPreparados, msgs>>

GRRecebeMsgEfetive(g) ==
  /\ [tipo |-> "Efetive"] \in msgs
  /\ estadoGR' = [estadoGR EXCEPT ![g] = "efetivado"]
  /\ UNCHANGED <<estadoGT, GRsPreparados, msgs>>

GRRecebeMsgAborte(g) ==
  /\ [tipo |-> "Aborte"] \in msgs
  /\ estadoGR' = [estadoGR EXCEPT ![g] = "abortado"]
  /\ UNCHANGED <<estadoGT, GRsPreparados, msgs>>

DFNext ==
  \/ GTEfetiva \/ GTAborta
  \/ \E g \in GR : 
       GTRecebePrepara(g) \/ GRPrepara(g) \/ GREcolheAbortar(g)
         \/ GRRecebeMsgEfetive(g) \/ GRRecebeMsgAborte(g)


THEOREM DFSpec => []DFTypeOK

INSTANCE TransacoesBD 

THEOREM DFSpec => TBDSpec

=============================================================================

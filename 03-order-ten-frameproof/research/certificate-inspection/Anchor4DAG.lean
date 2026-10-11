import DagLRAT
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
dag_lrat_files anchor4DagUnsat
  "research/direct-matrix/case-4-no-pairs-anchor.cnf"
  "research/certificate-inspection/anchor4.lrat"
#check anchor4DagUnsat
#print axioms anchor4DagUnsat

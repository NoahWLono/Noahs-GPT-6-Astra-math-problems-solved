import DagLRAT
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
dag_lrat_files anchor5DagUnsat
  "research/direct-matrix/case-5-no-pairs-anchor.cnf"
  "research/certificate-inspection/anchor5.lrat"
#check anchor5DagUnsat
#print axioms anchor5DagUnsat

import DagLRAT
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
dag_lrat_files anchor3DagUnsat
  "research/direct-matrix/case-3-no-pairs-anchor.cnf"
  "research/certificate-inspection/anchor3.lrat"
#check anchor3DagUnsat
#print axioms anchor3DagUnsat

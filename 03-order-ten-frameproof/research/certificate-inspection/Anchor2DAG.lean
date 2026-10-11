import DagLRAT
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
dag_lrat_files anchor2DagUnsat
  "research/direct-matrix/case-2-no-pairs-anchor.cnf"
  "research/certificate-inspection/anchor2.lrat"
#check anchor2DagUnsat
#print axioms anchor2DagUnsat

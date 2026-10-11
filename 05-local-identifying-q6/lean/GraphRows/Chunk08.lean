import GraphEncoding
namespace LocalIdentifyingQ6
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem sep_data_64 : separationClause (16,17) = [(1,true),(2,true),(19,true),(20,true),(21,true),(22,true),(25,true),(26,true),(49,true),(50,true)] := by decide +kernel
theorem sep_data_65 : separationClause (16,18) = [(1,true),(3,true),(18,true),(20,true),(21,true),(23,true),(25,true),(27,true),(49,true),(51,true)] := by decide +kernel
theorem sep_data_66 : separationClause (16,20) = [(1,true),(5,true),(18,true),(19,true),(22,true),(23,true),(25,true),(29,true),(49,true),(53,true)] := by decide +kernel
theorem sep_data_67 : separationClause (16,24) = [(1,true),(9,true),(18,true),(19,true),(21,true),(26,true),(27,true),(29,true),(49,true),(57,true)] := by decide +kernel
theorem sep_data_68 : separationClause (16,48) = [(1,true),(18,true),(19,true),(21,true),(25,true),(33,true),(50,true),(51,true),(53,true),(57,true)] := by decide +kernel
theorem sep_data_69 : separationClause (17,19) = [(2,true),(4,true),(17,true),(19,true),(22,true),(24,true),(26,true),(28,true),(50,true),(52,true)] := by decide +kernel
theorem sep_data_70 : separationClause (17,21) = [(2,true),(6,true),(17,true),(20,true),(21,true),(24,true),(26,true),(30,true),(50,true),(54,true)] := by decide +kernel
theorem sep_data_71 : separationClause (17,25) = [(2,true),(10,true),(17,true),(20,true),(22,true),(25,true),(28,true),(30,true),(50,true),(58,true)] := by decide +kernel
theorem sep_data_72 : separationClause (17,49) = [(2,true),(17,true),(20,true),(22,true),(26,true),(34,true),(49,true),(52,true),(54,true),(58,true)] := by decide +kernel
theorem sep_data_73 : separationClause (18,19) = [(3,true),(4,true),(17,true),(18,true),(23,true),(24,true),(27,true),(28,true),(51,true),(52,true)] := by decide +kernel
theorem sep_data_74 : separationClause (18,22) = [(3,true),(7,true),(17,true),(20,true),(21,true),(24,true),(27,true),(31,true),(51,true),(55,true)] := by decide +kernel
theorem sep_data_75 : separationClause (18,26) = [(3,true),(11,true),(17,true),(20,true),(23,true),(25,true),(28,true),(31,true),(51,true),(59,true)] := by decide +kernel
theorem sep_data_76 : separationClause (18,50) = [(3,true),(17,true),(20,true),(23,true),(27,true),(35,true),(49,true),(52,true),(55,true),(59,true)] := by decide +kernel
theorem sep_data_77 : separationClause (19,23) = [(4,true),(8,true),(18,true),(19,true),(22,true),(23,true),(28,true),(32,true),(52,true),(56,true)] := by decide +kernel
theorem sep_data_78 : separationClause (19,27) = [(4,true),(12,true),(18,true),(19,true),(24,true),(26,true),(27,true),(32,true),(52,true),(60,true)] := by decide +kernel
theorem sep_data_79 : separationClause (19,51) = [(4,true),(18,true),(19,true),(24,true),(28,true),(36,true),(50,true),(51,true),(56,true),(60,true)] := by decide +kernel
end LocalIdentifyingQ6

import GraphEncoding
namespace LocalIdentifyingQ6
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem sep_data_0 : separationClause (0,1) = [(3,true),(4,true),(5,true),(6,true),(9,true),(10,true),(17,true),(18,true),(33,true),(34,true)] := by decide +kernel
theorem sep_data_1 : separationClause (0,2) = [(2,true),(4,true),(5,true),(7,true),(9,true),(11,true),(17,true),(19,true),(33,true),(35,true)] := by decide +kernel
theorem sep_data_2 : separationClause (0,4) = [(2,true),(3,true),(6,true),(7,true),(9,true),(13,true),(17,true),(21,true),(33,true),(37,true)] := by decide +kernel
theorem sep_data_3 : separationClause (0,8) = [(2,true),(3,true),(5,true),(10,true),(11,true),(13,true),(17,true),(25,true),(33,true),(41,true)] := by decide +kernel
theorem sep_data_4 : separationClause (0,16) = [(2,true),(3,true),(5,true),(9,true),(18,true),(19,true),(21,true),(25,true),(33,true),(49,true)] := by decide +kernel
theorem sep_data_5 : separationClause (0,32) = [(2,true),(3,true),(5,true),(9,true),(17,true),(34,true),(35,true),(37,true),(41,true),(49,true)] := by decide +kernel
theorem sep_data_6 : separationClause (1,3) = [(1,true),(3,true),(6,true),(8,true),(10,true),(12,true),(18,true),(20,true),(34,true),(36,true)] := by decide +kernel
theorem sep_data_7 : separationClause (1,5) = [(1,true),(4,true),(5,true),(8,true),(10,true),(14,true),(18,true),(22,true),(34,true),(38,true)] := by decide +kernel
theorem sep_data_8 : separationClause (1,9) = [(1,true),(4,true),(6,true),(9,true),(12,true),(14,true),(18,true),(26,true),(34,true),(42,true)] := by decide +kernel
theorem sep_data_9 : separationClause (1,17) = [(1,true),(4,true),(6,true),(10,true),(17,true),(20,true),(22,true),(26,true),(34,true),(50,true)] := by decide +kernel
theorem sep_data_10 : separationClause (1,33) = [(1,true),(4,true),(6,true),(10,true),(18,true),(33,true),(36,true),(38,true),(42,true),(50,true)] := by decide +kernel
theorem sep_data_11 : separationClause (2,3) = [(1,true),(2,true),(7,true),(8,true),(11,true),(12,true),(19,true),(20,true),(35,true),(36,true)] := by decide +kernel
theorem sep_data_12 : separationClause (2,6) = [(1,true),(4,true),(5,true),(8,true),(11,true),(15,true),(19,true),(23,true),(35,true),(39,true)] := by decide +kernel
theorem sep_data_13 : separationClause (2,10) = [(1,true),(4,true),(7,true),(9,true),(12,true),(15,true),(19,true),(27,true),(35,true),(43,true)] := by decide +kernel
theorem sep_data_14 : separationClause (2,18) = [(1,true),(4,true),(7,true),(11,true),(17,true),(20,true),(23,true),(27,true),(35,true),(51,true)] := by decide +kernel
theorem sep_data_15 : separationClause (2,34) = [(1,true),(4,true),(7,true),(11,true),(19,true),(33,true),(36,true),(39,true),(43,true),(51,true)] := by decide +kernel
end LocalIdentifyingQ6

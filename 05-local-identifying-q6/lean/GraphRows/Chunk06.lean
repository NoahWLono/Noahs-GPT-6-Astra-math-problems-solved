import GraphEncoding
namespace LocalIdentifyingQ6
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem sep_data_32 : separationClause (6,38) = [(3,true),(5,true),(8,true),(15,true),(23,true),(35,true),(37,true),(40,true),(47,true),(55,true)] := by decide +kernel
theorem sep_data_33 : separationClause (7,15) = [(4,true),(6,true),(7,true),(12,true),(14,true),(15,true),(24,true),(32,true),(40,true),(48,true)] := by decide +kernel
theorem sep_data_34 : separationClause (7,23) = [(4,true),(6,true),(7,true),(16,true),(20,true),(22,true),(23,true),(32,true),(40,true),(56,true)] := by decide +kernel
theorem sep_data_35 : separationClause (7,39) = [(4,true),(6,true),(7,true),(16,true),(24,true),(36,true),(38,true),(39,true),(48,true),(56,true)] := by decide +kernel
theorem sep_data_36 : separationClause (8,9) = [(1,true),(2,true),(11,true),(12,true),(13,true),(14,true),(25,true),(26,true),(41,true),(42,true)] := by decide +kernel
theorem sep_data_37 : separationClause (8,10) = [(1,true),(3,true),(10,true),(12,true),(13,true),(15,true),(25,true),(27,true),(41,true),(43,true)] := by decide +kernel
theorem sep_data_38 : separationClause (8,12) = [(1,true),(5,true),(10,true),(11,true),(14,true),(15,true),(25,true),(29,true),(41,true),(45,true)] := by decide +kernel
theorem sep_data_39 : separationClause (8,24) = [(1,true),(10,true),(11,true),(13,true),(17,true),(26,true),(27,true),(29,true),(41,true),(57,true)] := by decide +kernel
theorem sep_data_40 : separationClause (8,40) = [(1,true),(10,true),(11,true),(13,true),(25,true),(33,true),(42,true),(43,true),(45,true),(57,true)] := by decide +kernel
theorem sep_data_41 : separationClause (9,11) = [(2,true),(4,true),(9,true),(11,true),(14,true),(16,true),(26,true),(28,true),(42,true),(44,true)] := by decide +kernel
theorem sep_data_42 : separationClause (9,13) = [(2,true),(6,true),(9,true),(12,true),(13,true),(16,true),(26,true),(30,true),(42,true),(46,true)] := by decide +kernel
theorem sep_data_43 : separationClause (9,25) = [(2,true),(9,true),(12,true),(14,true),(18,true),(25,true),(28,true),(30,true),(42,true),(58,true)] := by decide +kernel
theorem sep_data_44 : separationClause (9,41) = [(2,true),(9,true),(12,true),(14,true),(26,true),(34,true),(41,true),(44,true),(46,true),(58,true)] := by decide +kernel
theorem sep_data_45 : separationClause (10,11) = [(3,true),(4,true),(9,true),(10,true),(15,true),(16,true),(27,true),(28,true),(43,true),(44,true)] := by decide +kernel
theorem sep_data_46 : separationClause (10,14) = [(3,true),(7,true),(9,true),(12,true),(13,true),(16,true),(27,true),(31,true),(43,true),(47,true)] := by decide +kernel
theorem sep_data_47 : separationClause (10,26) = [(3,true),(9,true),(12,true),(15,true),(19,true),(25,true),(28,true),(31,true),(43,true),(59,true)] := by decide +kernel
end LocalIdentifyingQ6

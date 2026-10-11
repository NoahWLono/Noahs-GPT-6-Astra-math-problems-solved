import GraphEncoding
namespace LocalIdentifyingQ6
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem sep_data_16 : separationClause (3,7) = [(2,true),(3,true),(6,true),(7,true),(12,true),(16,true),(20,true),(24,true),(36,true),(40,true)] := by decide +kernel
theorem sep_data_17 : separationClause (3,11) = [(2,true),(3,true),(8,true),(10,true),(11,true),(16,true),(20,true),(28,true),(36,true),(44,true)] := by decide +kernel
theorem sep_data_18 : separationClause (3,19) = [(2,true),(3,true),(8,true),(12,true),(18,true),(19,true),(24,true),(28,true),(36,true),(52,true)] := by decide +kernel
theorem sep_data_19 : separationClause (3,35) = [(2,true),(3,true),(8,true),(12,true),(20,true),(34,true),(35,true),(40,true),(44,true),(52,true)] := by decide +kernel
theorem sep_data_20 : separationClause (4,5) = [(1,true),(2,true),(7,true),(8,true),(13,true),(14,true),(21,true),(22,true),(37,true),(38,true)] := by decide +kernel
theorem sep_data_21 : separationClause (4,6) = [(1,true),(3,true),(6,true),(8,true),(13,true),(15,true),(21,true),(23,true),(37,true),(39,true)] := by decide +kernel
theorem sep_data_22 : separationClause (4,12) = [(1,true),(6,true),(7,true),(9,true),(14,true),(15,true),(21,true),(29,true),(37,true),(45,true)] := by decide +kernel
theorem sep_data_23 : separationClause (4,20) = [(1,true),(6,true),(7,true),(13,true),(17,true),(22,true),(23,true),(29,true),(37,true),(53,true)] := by decide +kernel
theorem sep_data_24 : separationClause (4,36) = [(1,true),(6,true),(7,true),(13,true),(21,true),(33,true),(38,true),(39,true),(45,true),(53,true)] := by decide +kernel
theorem sep_data_25 : separationClause (5,7) = [(2,true),(4,true),(5,true),(7,true),(14,true),(16,true),(22,true),(24,true),(38,true),(40,true)] := by decide +kernel
theorem sep_data_26 : separationClause (5,13) = [(2,true),(5,true),(8,true),(10,true),(13,true),(16,true),(22,true),(30,true),(38,true),(46,true)] := by decide +kernel
theorem sep_data_27 : separationClause (5,21) = [(2,true),(5,true),(8,true),(14,true),(18,true),(21,true),(24,true),(30,true),(38,true),(54,true)] := by decide +kernel
theorem sep_data_28 : separationClause (5,37) = [(2,true),(5,true),(8,true),(14,true),(22,true),(34,true),(37,true),(40,true),(46,true),(54,true)] := by decide +kernel
theorem sep_data_29 : separationClause (6,7) = [(3,true),(4,true),(5,true),(6,true),(15,true),(16,true),(23,true),(24,true),(39,true),(40,true)] := by decide +kernel
theorem sep_data_30 : separationClause (6,14) = [(3,true),(5,true),(8,true),(11,true),(13,true),(16,true),(23,true),(31,true),(39,true),(47,true)] := by decide +kernel
theorem sep_data_31 : separationClause (6,22) = [(3,true),(5,true),(8,true),(15,true),(19,true),(21,true),(24,true),(31,true),(39,true),(55,true)] := by decide +kernel
end LocalIdentifyingQ6

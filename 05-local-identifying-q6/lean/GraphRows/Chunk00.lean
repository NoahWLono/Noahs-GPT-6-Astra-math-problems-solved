import GraphEncoding
namespace LocalIdentifyingQ6
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem dom_data_0 : dominationClause 0 = [(1,true),(2,true),(3,true),(5,true),(9,true),(17,true),(33,true)] := by decide +kernel
theorem dom_data_1 : dominationClause 1 = [(1,true),(2,true),(4,true),(6,true),(10,true),(18,true),(34,true)] := by decide +kernel
theorem dom_data_2 : dominationClause 2 = [(1,true),(3,true),(4,true),(7,true),(11,true),(19,true),(35,true)] := by decide +kernel
theorem dom_data_3 : dominationClause 3 = [(2,true),(3,true),(4,true),(8,true),(12,true),(20,true),(36,true)] := by decide +kernel
theorem dom_data_4 : dominationClause 4 = [(1,true),(5,true),(6,true),(7,true),(13,true),(21,true),(37,true)] := by decide +kernel
theorem dom_data_5 : dominationClause 5 = [(2,true),(5,true),(6,true),(8,true),(14,true),(22,true),(38,true)] := by decide +kernel
theorem dom_data_6 : dominationClause 6 = [(3,true),(5,true),(7,true),(8,true),(15,true),(23,true),(39,true)] := by decide +kernel
theorem dom_data_7 : dominationClause 7 = [(4,true),(6,true),(7,true),(8,true),(16,true),(24,true),(40,true)] := by decide +kernel
theorem dom_data_8 : dominationClause 8 = [(1,true),(9,true),(10,true),(11,true),(13,true),(25,true),(41,true)] := by decide +kernel
theorem dom_data_9 : dominationClause 9 = [(2,true),(9,true),(10,true),(12,true),(14,true),(26,true),(42,true)] := by decide +kernel
theorem dom_data_10 : dominationClause 10 = [(3,true),(9,true),(11,true),(12,true),(15,true),(27,true),(43,true)] := by decide +kernel
theorem dom_data_11 : dominationClause 11 = [(4,true),(10,true),(11,true),(12,true),(16,true),(28,true),(44,true)] := by decide +kernel
theorem dom_data_12 : dominationClause 12 = [(5,true),(9,true),(13,true),(14,true),(15,true),(29,true),(45,true)] := by decide +kernel
theorem dom_data_13 : dominationClause 13 = [(6,true),(10,true),(13,true),(14,true),(16,true),(30,true),(46,true)] := by decide +kernel
theorem dom_data_14 : dominationClause 14 = [(7,true),(11,true),(13,true),(15,true),(16,true),(31,true),(47,true)] := by decide +kernel
theorem dom_data_15 : dominationClause 15 = [(8,true),(12,true),(14,true),(15,true),(16,true),(32,true),(48,true)] := by decide +kernel
end LocalIdentifyingQ6

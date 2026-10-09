import Definitions
open FastWalsh
namespace N12.C008
def data0_0 : Tree 0 := .leaf (1)
def data0_1 : Tree 0 := .leaf (-1)
def data1_0 : Tree 1 := .node data0_0 data0_0
def data1_1 : Tree 1 := .node data0_1 data0_1
def data2_0 : Tree 2 := .node data1_0 data1_0
def data2_1 : Tree 2 := .node data1_1 data1_1
def data3_0 : Tree 3 := .node data2_0 data2_0
def data3_1 : Tree 3 := .node data2_1 data2_1
def data4_0 : Tree 4 := .node data3_0 data3_0
def data4_1 : Tree 4 := .node data3_0 data3_1
def data4_2 : Tree 4 := .node data3_1 data3_1
def data4_3 : Tree 4 := .node data3_1 data3_0
def data5_0 : Tree 5 := .node data4_0 data4_0
def data5_1 : Tree 5 := .node data4_1 data4_1
def data5_2 : Tree 5 := .node data4_2 data4_2
def data5_3 : Tree 5 := .node data4_3 data4_3
def data5_4 : Tree 5 := .node data4_0 data4_2
def data5_5 : Tree 5 := .node data4_1 data4_3
def data5_6 : Tree 5 := .node data4_2 data4_0
def data5_7 : Tree 5 := .node data4_3 data4_1
def data6_0 : Tree 6 := .node data5_0 data5_0
def data6_1 : Tree 6 := .node data5_1 data5_1
def data6_2 : Tree 6 := .node data5_0 data5_2
def data6_3 : Tree 6 := .node data5_1 data5_3
def data6_4 : Tree 6 := .node data5_4 data5_4
def data6_5 : Tree 6 := .node data5_5 data5_5
def data6_6 : Tree 6 := .node data5_4 data5_6
def data6_7 : Tree 6 := .node data5_5 data5_7
def data7_0 : Tree 7 := .node data6_0 data6_1
def data7_1 : Tree 7 := .node data6_2 data6_3
def data7_2 : Tree 7 := .node data6_4 data6_5
def data7_3 : Tree 7 := .node data6_6 data6_7
def data8_0 : Tree 8 := .node data7_0 data7_1
def data8_1 : Tree 8 := .node data7_2 data7_3
def data9_0 : Tree 9 := .node data8_0 data8_1
def data10_0 : Tree 10 := .node data9_0 data9_0
def data11_0 : Tree 11 := .node data10_0 data10_0
def data12_0 : Tree 12 := .node data11_0 data11_0
def inputTree : Tree 12 := data12_0
end N12.C008

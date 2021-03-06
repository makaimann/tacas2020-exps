`ifndef FF
`define FF

module FF(rst, clk, en, D, Q);
   parameter WIDTH = 1;
   parameter INIT  = 0;

   input wire                rst;
   input wire                clk;
   input wire                en;
   input wire [WIDTH-1:0]    D;

   output reg [WIDTH-1:0]    Q;

   always @ (posedge clk) begin
      if (rst) begin
         Q <= INIT;
      end
      else if(en) begin
         Q <= D;
      end
   end
endmodule
`endif

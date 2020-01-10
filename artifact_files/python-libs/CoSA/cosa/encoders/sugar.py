# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pysmt.shortcuts import Not, And, get_type, BV, EqualsOrIff, Select, get_env, get_type
from pysmt.parsing import Rule, UnaryOpAdapter, InfixOpAdapter, FunctionCallAdapter
from cosa.utils.logger import Logger
from cosa.representation import TS
from cosa.encoders.template import SyntacticSugar
from cosa.utils.formula_mngm import BV2B, B2BV, mem_access

class Posedge(SyntacticSugar):
    name = "posedge"
    description = "Clock Posedge"
    interface = "variable"

    def adapter(self):
        return UnaryOpAdapter(self.Posedge, 100)

    def Posedge(self, x):
        if get_type(x).is_bool_type():
            if (self.encoder_config is not None) and (self.encoder_config.abstract_clock):
                return x
            return And(Not(x), TS.to_next(x))
        if (self.encoder_config is not None) and (self.encoder_config.abstract_clock):
            return EqualsOrIff(x, BV(1,1))
        return And(EqualsOrIff(x, BV(0,1)), BV2B(TS.to_next(x)))

class Negedge(SyntacticSugar):
    name = "negedge"
    description = "Clock Negedge"
    interface = "variable"

    def adapter(self):
        return UnaryOpAdapter(self.Negedge, 100)

    def Negedge(self, x):
        if get_type(x).is_bool_type():
            if (self.encoder_config is not None) and (self.encoder_config.abstract_clock):
                return Not(x)
            return And(x, Not(TS.to_next(x)))
        if (self.encoder_config is not None) and (self.encoder_config.abstract_clock):
            return EqualsOrIff(x, BV(0,1))
        return And(BV2B(x), EqualsOrIff(TS.to_next(x), BV(0,1)))

class Change(SyntacticSugar):
    name = "change"
    description = "Signal Changes"
    interface = "variable"

    def adapter(self):
        return UnaryOpAdapter(self.Change, 100)

    def Change(self, x):
        return Not(EqualsOrIff(x), TS.to_next(x))

class NoChange(SyntacticSugar):
    name = "nochange"
    description = "Signal doesn't Change"
    interface = "variable"

    def adapter(self):
        return UnaryOpAdapter(self.NoChange, 100)

    def NoChange(self, x):
        return EqualsOrIff(x, TS.to_next(x))

class Ones(SyntacticSugar):
    name = "ones"
    description = "Maximum Bitvector value"
    interface = "variable"

    def adapter(self):
        return UnaryOpAdapter(self.Ones, 100)

    def Ones(self, x):
        if type(x) == int:
            return BV((2**x)-1,x)
        size = get_type(x).width
        return BV((2**size)-1,size)

class Zero(SyntacticSugar):
    name = "zero"
    description = "Zero value"
    interface = "variable"

    def adapter(self):
        return UnaryOpAdapter(self.Zero, 100)

    def Zero(self, x):
        if type(x) == int:
            return BV(0,x)
        size = get_type(x).width
        return BV(0,size)

class Dec2BV(SyntacticSugar):
    name = "dec2bv"
    description = "Decimal to BitVector"
    interface = "value, variable"

    def adapter(self):
        return FunctionCallAdapter(self.Dec2BV, 60)

    def Dec2BV(self, left, right):
        if right.is_int_constant():
            size = right.constant_value()
        else:
            size = get_type(right).width

        if not left.is_int_constant():
            Logger.error("Left argument of dec2bv should be a number")

        return BV(left.constant_value(), size)

class MemAccess(SyntacticSugar):
    name = "memacc"
    description = "Memory Access"
    interface = "memory, location"

    def adapter(self):
        return FunctionCallAdapter(self.MemAcc, 60)

    def MemAcc(self, left, right):
        ltype = left.get_type()
        assert ltype.is_array_type()

        if right.is_constant() and right.get_type().is_int_type():
            right = BV(right.constant_value(), ltype.index_type.width)

        return Select(left, right)

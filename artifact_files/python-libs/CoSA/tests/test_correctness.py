# Copyright 2018 Cristian Mattarei
#
# Licensed under the modified BSD (3-clause BSD) License.
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import os

from cosa.environment import reset_env
from cosa.options import cosa_option_manager
from cosa.shell import run_problems

COSADIR = ".CoSA"

abspath = os.path.abspath(__file__)
path = ("/".join(abspath.split("/")[:-1]))
testdirs = [d[0] for d in os.walk(path) if d[0] != path and "__" not in d[0] and COSADIR not in d[0]]

problem_files = []
for testdir in testdirs:
    for problem in [p for p in list(os.walk(testdir))[0][2] if "problem" in p and ".txt" == p[-4:]]:
        problem_files.append("%s/%s"%(testdir, problem))
problem_files.sort()
problem_files.reverse()

def runtest(problem_file):
    reset_env()
    translate_file = 'file.ssts'
    problems_manager = cosa_option_manager.read_problem_file(problem_file,
                                                             verbosity=2,
                                                             solver_name='msat',
                                                             prove=True,
                                                             vcd=True,
                                                             translate=translate_file)

    # run option handling code then freeze problem manager
    # TODO: Update this to make a better API
    # problems_manager modified in place
    cosa_option_manager._option_handling(problems_manager)
    problems_manager.freeze()

    status = run_problems(problems_manager)
    with open(translate_file, "r") as f:
        print(f.read())

    assert status == 0
    return status

def test_problem():
    for problem_file in problem_files:
        yield runtest, problem_file

if __name__ == "__main__":
    for problem_file in problem_files:
        runtest(problem_file)

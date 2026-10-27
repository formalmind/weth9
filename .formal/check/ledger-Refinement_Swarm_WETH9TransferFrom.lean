import Refinement.Swarm.WETH9TransferFrom
#print "fm-ledger 0"
#check @WETH9.Swarm.TF.transferFrom_reverts_balance
#print axioms WETH9.Swarm.TF.transferFrom_reverts_balance
#print "fm-ledger 1"
#check @WETH9.Swarm.TF.transferFrom_reverts_allowance
#print axioms WETH9.Swarm.TF.transferFrom_reverts_allowance
#print "fm-ledger 2"
#check @WETH9.Swarm.TF.transferFrom_succeeds_spend
#print axioms WETH9.Swarm.TF.transferFrom_succeeds_spend
#print "fm-ledger 3"
#check @WETH9.Swarm.TF.transferFrom_succeeds_nospend
#print axioms WETH9.Swarm.TF.transferFrom_succeeds_nospend

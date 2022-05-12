# because for some reason stack messes this up and removes the executable's 
# dependency on lh-tactics...
cp lh-tactics.cabal-correct lh-tactics.cabal

stack build 
stack install
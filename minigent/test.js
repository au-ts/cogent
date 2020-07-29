var C = require('./minigent.js');
var A = require('./abstract.js');
function height (r) { return C.Case((r).node, "Leaf", u=>0,node2=>C.Let((node2).val, tree=>C.Let(height((tree).left),left=>C.Let(height((tree).right),right=>((left > right) ? (left + 1) : (right + 1)))))); };



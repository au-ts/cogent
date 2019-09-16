function Let(x,f) {
  return f(x);
}

function UPut(o,upds) {
  var o2 = Object.assign({},o);
  return Object.assign(o2,upds);
}

function Case(v,t,thn,els) {
  if (v.tag == t) {
    return thn(v.val);
  } else {
    return els(v);
  }
}

exports.Let = Let;
exports.UPut = UPut;
exports.Case = Case;

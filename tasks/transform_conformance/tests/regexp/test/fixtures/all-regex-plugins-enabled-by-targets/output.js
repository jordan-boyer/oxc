x1 = new RegExp(".", "y");
x2 = new RegExp(".", "u");
a1 = new RegExp("a.b", "s");
b1 = new RegExp("(?<!x)", "");
b2 = new RegExp("(?<=x)", "");
b3 = new RegExp("((?<!x)){2}", "");
b4 = new RegExp("((?<=x)){3}", "");
c1 = new RegExp("(?<a>b)", "");
c2 = new RegExp("((?<c>d)){4}", "");
d1 = new RegExp("\\p{Emoji}", "u");
f1 = new RegExp("y", "d");
g1 = new RegExp("[\\p{White_Space}&&\\p{ASCII}]", "v");
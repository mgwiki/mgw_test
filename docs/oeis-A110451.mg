<html><head>
<style>
.paramdecl {
 margin-top: 3px;
 margin-bottom: 3px;
}
.defdecl {
 margin-top: 3px;
 margin-bottom: 3px;
}
.axdecl {
 margin-top: 3px;
 margin-bottom: 3px;
}
.thmdecl {
 margin-top: 3px;
 margin-bottom: 3px;
}
.proof {
 border-style: solid;
 border-width: 2px;
 padding: 1px;
 margin: 1px;
}
.subproof {
 border-style: solid;
 border-width: 1px;
 padding: 1px;
 margin: 1px;
}
.section {
 border-style: solid;
 border-width: 2px;
 padding: 1px;
 margin: 1px;
}
.sectionbegin {
 text-align: center;
 text-decoration: underline;
}
.sectionend {
 text-align: center;
 text-decoration: underline;
}
</style>
</head><body>
<div class='section'>
<div class='sectionbegin'>Beginning of Section <b>A110451</b></div>
<div class='prefixdecl'><a name='notation_1'/><b>Notation</b>. We use <span class='ltree'>-</span> as a prefix operator with priority 358 corresponding to applying term <span class='ltree'><span class='ltree'>minus_SNo</span></span>.</div>
<div class='infixdecl'><a name='notation_2'/><b>Notation</b>. We use <span class='ltree'>+</span> as an infix operator with priority 360 and which associates to the right corresponding to applying term <span class='ltree'><span class='ltree'>add_SNo</span></span>.</div>
<div class='infixdecl'><a name='notation_3'/><b>Notation</b>. We use <span class='ltree'>*</span> as an infix operator with priority 355 and which associates to the right corresponding to applying term <span class='ltree'><span class='ltree'>mul_SNo</span></span>.</div>
<div class='infixdecl'><a name='notation_4'/><b>Notation</b>. We use <span class='ltree'><</span> as an infix operator with priority 490 and no associativity corresponding to applying term <span class='ltree'><span class='ltree'>SNoLt</span></span>.</div>
<div class='infixdecl'><a name='notation_5'/><b>Notation</b>. We use <span class='ltree'><=</span> as an infix operator with priority 490 and no associativity corresponding to applying term <span class='ltree'><span class='ltree'>SNoLe</span></span>.</div>
<div class='vardecl'><span class='docitemkeyword'>Variable</span> <span class='ltree'> F0 : <span class='ltree'><span class='ltree'>set</span> &#x2192; <span class='ltree'><span class='ltree'>set</span> &#x2192; <span class='ltree'>set</span></span></span></span></div>
<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>HF0 : <span class='ltree'><a href='#In_notation'>&#x2200;</a>x0<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'><a href='#In_notation'>&#x2200;</a>x1<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'><span class='ltree'><span class='ltree'><span class='ltree'>F0</span> <span class='ltree'>x0</span></span> <span class='ltree'>x1</span></span>  <a href='#In_notation'>&#x2208;</a>  <span class='ltree'>int</span></span></span></span></span></div>
<div class='vardecl'><span class='docitemkeyword'>Variable</span> <span class='ltree'> G0 : <span class='ltree'><span class='ltree'>set</span> &#x2192; <span class='ltree'>set</span></span></span></div>
<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>HG0 : <span class='ltree'><a href='#In_notation'>&#x2200;</a>x0<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'><span class='ltree'><span class='ltree'>G0</span> <span class='ltree'>x0</span></span>  <a href='#In_notation'>&#x2208;</a>  <span class='ltree'>int</span></span></span></span></div>
<div class='vardecl'><span class='docitemkeyword'>Variable</span> <span class='ltree'> H0 : <span class='ltree'>set</span></span></div>
<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>HH0 : <span class='ltree'><span class='ltree'>H0</span>  <a href='#In_notation'>&#x2208;</a>  <span class='ltree'>int</span></span></span></div>
<div class='vardecl'><span class='docitemkeyword'>Variable</span> <span class='ltree'> U0 : <span class='ltree'><span class='ltree'>set</span> &#x2192; <span class='ltree'><span class='ltree'>set</span> &#x2192; <span class='ltree'>set</span></span></span></span></div>
<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>HU0 : <span class='ltree'><a href='#In_notation'>&#x2200;</a>x0<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'><a href='#In_notation'>&#x2200;</a>x1<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'><span class='ltree'><span class='ltree'><span class='ltree'>U0</span> <span class='ltree'>x0</span></span> <span class='ltree'>x1</span></span>  <a href='#In_notation'>&#x2208;</a>  <span class='ltree'>int</span></span></span></span></span></div>
<div class='vardecl'><span class='docitemkeyword'>Variable</span> <span class='ltree'> V0 : <span class='ltree'><span class='ltree'>set</span> &#x2192; <span class='ltree'>set</span></span></span></div>
<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>HV0 : <span class='ltree'><a href='#In_notation'>&#x2200;</a>x0<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'><span class='ltree'><span class='ltree'>V0</span> <span class='ltree'>x0</span></span>  <a href='#In_notation'>&#x2208;</a>  <span class='ltree'>int</span></span></span></span></div>
<div class='vardecl'><span class='docitemkeyword'>Variable</span> <span class='ltree'> SMALL : <span class='ltree'><span class='ltree'>set</span> &#x2192; <span class='ltree'>set</span></span></span></div>
<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>HSMALL : <span class='ltree'><a href='#In_notation'>&#x2200;</a>x0<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'><span class='ltree'><span class='ltree'>SMALL</span> <span class='ltree'>x0</span></span>  <a href='#In_notation'>&#x2208;</a>  <span class='ltree'>int</span></span></span></span></div>
<div class='vardecl'><span class='docitemkeyword'>Variable</span> <span class='ltree'> FAST : <span class='ltree'><span class='ltree'>set</span> &#x2192; <span class='ltree'>set</span></span></span></div>
<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>HFAST : <span class='ltree'><a href='#In_notation'>&#x2200;</a>x0<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'><span class='ltree'><span class='ltree'>FAST</span> <span class='ltree'>x0</span></span>  <a href='#In_notation'>&#x2208;</a>  <span class='ltree'>int</span></span></span></span></div>
<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>H1 : <span class='ltree'>(<span class='ltree'><a href='#In_notation'>&#x2200;</a>X<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'>(<span class='ltree'><a href='#In_notation'>&#x2200;</a>Y<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'>(<span class='ltree'><span class='ltree'>(<span class='ltree'><span class='ltree'><span class='ltree'>F0</span> <span class='ltree'>X</span></span> <span class='ltree'>Y</span></span>)</span> = <span class='ltree'>(<span class='ltree'><span class='ltree'>(<span class='ltree'><span class='ltree'>X</span> <a href='#notation_2'>+</a> <span class='ltree'>Y</span></span>)</span> <a href='#notation_2'>+</a> <span class='ltree'>Y</span></span>)</span></span>)</span></span>)</span></span>)</span></span></div>
<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>H2 : <span class='ltree'>(<span class='ltree'><a href='#In_notation'>&#x2200;</a>X<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'>(<span class='ltree'><span class='ltree'>(<span class='ltree'><span class='ltree'>G0</span> <span class='ltree'>X</span></span>)</span> = <span class='ltree'>(<span class='ltree'><span class='ltree'>X</span> <a href='#notation_2'>+</a> <span class='ltree'>X</span></span>)</span></span>)</span></span>)</span></span></div>
<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>H3 : <span class='ltree'>(<span class='ltree'><span class='ltree'>H0</span> = <span class='ltree'>1</span></span>)</span></span></div>
<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>H4 : <span class='ltree'>(<span class='ltree'><a href='#In_notation'>&#x2200;</a>X<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'>(<span class='ltree'><a href='#In_notation'>&#x2200;</a>Y<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'>(<span class='ltree'><span class='ltree'>(<span class='ltree'><span class='ltree'><span class='ltree'>U0</span> <span class='ltree'>X</span></span> <span class='ltree'>Y</span></span>)</span> = <span class='ltree'>(<span class='ltree'><span class='keyword'>if</span> <span class='ltree'>(<span class='ltree'><span class='ltree'>X</span> <a href='#notation_5'><=</a> <span class='ltree'>0</span></span>)</span> <span class='keyword'>then</span> <span class='ltree'>Y</span> <span class='keyword'>else</span> <span class='ltree'>(<span class='ltree'><span class='ltree'><span class='ltree'>F0</span> <span class='ltree'>(<span class='ltree'><span class='ltree'><span class='ltree'>U0</span> <span class='ltree'>(<span class='ltree'><span class='ltree'>X</span> <a href='#notation_2'>+</a> <span class='ltree'><a href='#notation_1'>-</a> <span class='ltree'>1</span></span></span>)</span></span> <span class='ltree'>Y</span></span>)</span></span> <span class='ltree'>X</span></span>)</span></span>)</span></span>)</span></span>)</span></span>)</span></span></div>
<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>H5 : <span class='ltree'>(<span class='ltree'><a href='#In_notation'>&#x2200;</a>X<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'>(<span class='ltree'><span class='ltree'>(<span class='ltree'><span class='ltree'>V0</span> <span class='ltree'>X</span></span>)</span> = <span class='ltree'>(<span class='ltree'><span class='ltree'><span class='ltree'>U0</span> <span class='ltree'>(<span class='ltree'><span class='ltree'>G0</span> <span class='ltree'>X</span></span>)</span></span> <span class='ltree'>H0</span></span>)</span></span>)</span></span>)</span></span></div>
<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>H6 : <span class='ltree'>(<span class='ltree'><a href='#In_notation'>&#x2200;</a>X<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'>(<span class='ltree'><span class='ltree'>(<span class='ltree'><span class='ltree'>SMALL</span> <span class='ltree'>X</span></span>)</span> = <span class='ltree'>(<span class='ltree'><span class='ltree'>(<span class='ltree'><span class='ltree'>V0</span> <span class='ltree'>X</span></span>)</span> <a href='#notation_3'>*</a> <span class='ltree'>X</span></span>)</span></span>)</span></span>)</span></span></div>
<div class='hypdecl'><span class='docitemkeyword'>Hypothesis</span> <span class='ltree'>H7 : <span class='ltree'>(<span class='ltree'><a href='#In_notation'>&#x2200;</a>X<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'>(<span class='ltree'><span class='ltree'>(<span class='ltree'><span class='ltree'>FAST</span> <span class='ltree'>X</span></span>)</span> = <span class='ltree'>(<span class='ltree'><span class='ltree'>(<span class='ltree'><span class='ltree'>2</span> <a href='#notation_3'>*</a> <span class='ltree'>(<span class='ltree'><span class='ltree'>(<span class='ltree'><span class='ltree'>1</span> <a href='#notation_2'>+</a> <span class='ltree'>(<span class='ltree'><span class='ltree'>X</span> <a href='#notation_2'>+</a> <span class='ltree'>X</span></span>)</span></span>)</span> <a href='#notation_3'>*</a> <span class='ltree'>(<span class='ltree'><span class='ltree'>X</span> <a href='#notation_3'>*</a> <span class='ltree'>X</span></span>)</span></span>)</span></span>)</span> <a href='#notation_2'>+</a> <span class='ltree'>X</span></span>)</span></span>)</span></span>)</span></span></div>
<a name='A110451'/><div class='thmandproof'><div class='thmdecl'><b>Theorem.</b> (<span class='ltree'><a classname='anamelink' href='#A110451'>A110451</a></span>) The following is provable: <div class='thmprop'><span class='ltree'><span class='ltree'>(<span class='ltree'><a href='#In_notation'>&#x2200;</a>N<a href='#In_notation'> &#x2208; </a><span class='ltree'>int</span><a href='#In_notation'>, </a> <span class='ltree'>(<span class='ltree'><span class='ltree'>(<span class='ltree'><span class='ltree'>0</span> <a href='#notation_5'><=</a> <span class='ltree'>N</span></span>)</span> &#x2192; <span class='ltree'>(<span class='ltree'><span class='ltree'>(<span class='ltree'><span class='ltree'>SMALL</span> <span class='ltree'>N</span></span>)</span> = <span class='ltree'>(<span class='ltree'><span class='ltree'>FAST</span> <span class='ltree'>N</span></span>)</span></span>)</span></span>)</span></span>)</span></span></div></div>
<div class='pfglinks'>In Proofgold the corresponding term root is <a href='https://project-smart.uibk.ac.at/pgbce/q.php?b=9fb3494f655a77dce0c303a51509df063983d4b6a73baf0289a30bf5a30e0c60'>9fb349...</a> and proposition id is <a href='https://project-smart.uibk.ac.at/pgbce/q.php?b=3d9138212d774ec3a51bc3594ee1ae912bfe7cebcba8ac0b1f003b22a632f9e7'>3d9138...</a></div>
<div id='pf1' class='proof'><div class='proofpres' onclick='g(this)'><b>Proof:</b><br/><div class='admitted'>The proof is left to the reader.</div>
</div><div id='pf1code' class='proofcodehidden'>
<input type='hidden' id='pf1codeline' value='0'/><input type='hidden' id='pf1codechar' value='0'/>
<textarea id='pf1codetext' rows=5 cols=80></textarea><br/><input type='button' value='Check' onclick='h(this)'/>
<div id='pf1coderesp' class='proofcoderesp'/></div></div></div></div>
<div class='sectionend'>End of Section <b>A110451</b></div>
</div>
</body></html>
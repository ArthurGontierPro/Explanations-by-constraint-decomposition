function feuille(tab)
    m=0;im=0
    for i in 2:size(e,1)
        if m<length(e[i][1])&&!(e[i][2][1] in ['T','F','?','∀','∃'])&&!(i in tab)
            im = i
            m = length(e[i][1])
        end
    end
    return im
end
function printe(verbose=false)
    print(" ",e[1][2]," <- ")
    tab=[]
    im = feuille(tab)
    ou = ""
    while im>0
        c=[]
        for i in 2:size(e,1)
            for ii in 0:length(e[im][1])-1#;println(e[i][1],"  ",e[im][1][1:end-ii])
                if e[i][1] == e[im][1][1:end-ii]
                    push!(c,e[i][2])
                    push!(tab,i)
                end
            end
        end
        im = feuille(tab)
        if !('?' in c)&&!('F' in c)
            print(ou)
            for v in c
                if verbose || !(v[1] in ['T','F','?'])
                    if v[1] in ['∀','∃']
                        print(v," ")
                    else
                        print(v,"   ")
                    end
                end
            end
            if im !=0
                ou = "\n       ∨ "
            end
        end
    end
    println()
end
function printc(c)
    s=c[1][1]
    for i in 2:size(c,1)
        ss=""
        for j in 1:size(c[i][2],1)
            ss=ss*c[i][2][j]
        end
        s=s*c[i][1]*ss*"--"
    end
    return s
end
function id(x)
    return x
end
function n(var)
    return if var[1]=='n' var[2:end] else string('n',var) end
end
function ap(te,v,c)
    i=te[2](v[2])
    if i[end][1]=='∃' || i[end][1]=='∀'
        push!(e,(c[1][1],i[end]))
        i = i[1:end-1]
    end
    return (te[1],i)
end
function nap(te,v,c)
    i=te[2](v[2])
    if i[end][1]=='∃' || i[end][1]=='∀'
        push!(e,(c[1][1],i[end]))
        i = i[1:end-1]
    end
    return (n(te[1]),i)
end
function literal(v,i,sy)
    s = v
    for k in 1:size(i,1)-1
        s = s*i[k]
    end
    return s*sy*i[end]
end
function im(eqv,v)
    return setdiff(ap(eqv,v,[])[2],v[2])[1]
end
function find(v,prec,dec,c)#;printe(true)
    f = 1
    if !((n(v[1]),id(v[2])) in map(v->(v[1],v[2]),c))&&!(v in map(v->(v[1],v[2]),c))
        for i in 1:size(dec,1)
            if i!=prec
                if !((v[1],i) in map(v->(v[1],v[3]),c))&&!((n(v[1]),i) in map(v->(v[1],v[3]),c))
                    for j in 1:size(dec[i][2],1)
                        if v[1]==dec[i][2][j][1] || n(v[1])==dec[i][2][j][1]
                            cc=push!(copy(c),(v[1],v[2],i))
                            cc[1]=(cc[1][1]*string(f),[],1);f=f+1
                            dec[i][1](v,i,dec,j,cc)
                        end
                    end
                end
            end
        end
    end
end
function rule1(v,i,dec,j,c)
    eq = dec[i][2]
    if v[1]==eq[1][1]
        find(ap(eq[2],v,c),i,dec,c)
    elseif v[1]==n(eq[1][1])
        find(nap(eq[2],v,c),i,dec,c)
    elseif v[1]==eq[end][1]
        push!(e,(c[1][1],literal(eq[1][1],v[2],'=')))
    else
        push!(e,(c[1][1],literal(eq[1][1],v[2],'≠')))
    end
end
function rule2(v,i,dec,j,c)
    eq = dec[i][2]
    if v[1]==eq[1][1]
        find(ap(eq[2],v,c),i,dec,c)
    elseif v[1]==n(eq[1][1])
        find(nap(eq[2],v,c),i,dec,c)
    elseif v[1]==eq[end][1]
        push!(e,(c[1][1],literal(eq[1][1],v[2],'≥')))
    else
        push!(e,(c[1][1],literal(eq[1][1],v[2],'<')))
    end
end
function rule3(v,i,dec,j,c)
    eq = dec[i][2]
    bigg = size(eq,1)==2
    if j<size(eq,1)
        if v[1]==eq[j][1]
            if eq[end][1]!="true"
                find(ap(eq[end],v,c),i,dec,c)
            else
                push!(e,(c[1][1],'T'))
            end
        end
        if v[1]==n(eq[j][1])
            if eq[end][1]!="true"
                find(nap(eq[end],v,c),i,dec,c)
                if bigg 
                    push!(e,(c[1][1],string("∀",im(eq[1],v))))
                    find(ap(eq[1],v,c),i,dec,c)
                else
                    for jj in 1:size(eq,1)-1
                        if j != jj
                            find(ap(eq[jj],v,c),i,dec,c)
                        end
                    end
                end
            else
                push!(e,(c[1][1],'F'))
            end
        end
    else
        if v[1]==eq[end][1]
            for jj in 1:size(eq,1)-1
                if bigg push!(e,(c[1][1],string("∀",im(eq[jj],v)))) end
                find(ap(eq[jj],v,c),i,dec,c)
            end
        end
        if v[1]==n(eq[end][1])
            for jj in 1:size(eq,1)-1
                if bigg push!(e,(c[1][1],string("∃",im(eq[jj],v)))) end
                find(nap(eq[jj],v,c),i,dec,c)            
            end
        end
    end
end
function rule4(v,i,dec,j,c)
    eq = dec[i][2]
    bigg = size(eq,1)==2
    if j<size(eq,1)
        if v[1]==eq[j][1]
            if bigg 
                push!(e,(c[1][1],string("∀",im(eq[1],v))))
                find(nap(eq[1],v,c),i,dec,c)
            else            
                for jj in 1:size(eq,1)-1
                    if j != jj
                        find(nap(eq[jj],v,c),i,dec,c)
                    end
                end
            end
            if eq[end][1]!="true"
                find(ap(eq[end],v,c),i,dec,c)
            else
                push!(e,(c[1][1],'T'))
            end
        end
        if v[1]==n(eq[j][1])
            if eq[end][1]!="true"
                find(nap(eq[end],v,c),i,dec,c)
            else
                push!(e,(c[1][1],'?'))
            end
        end
    else
        if v[1]==eq[end][1]
            for jj in 1:size(eq,1)-1
                if bigg push!(e,(c[1][1],string("∃",im(eq[jj],v)))) end
                find(ap(eq[jj],v,c),i,dec,c)
            end
        end
        if v[1]==n(eq[end][1])
            for jj in 1:size(eq,1)-1
                if bigg push!(e,(c[1][1],string("∀",im(eq[jj],v)))) end
                find(nap(eq[jj],v,c),i,dec,c)
            end
        end
    end
end
function rule5(v,i,dec,j,c)
    eq = dec[i][2]
    if v[1]==n(eq[1][1])
        push!(e,(c[1][1],string("∀",im(eq[1],v))))
        find(ap(eq[1],v,c),i,dec,c)
        if eq[end][1]!="true"
            find(ap(eq[end],v,c),i,dec,c)
        else
            push!(e,(c[1][1],'T'))
        end
    else
        push!(e,(c[1][1],'?'))
    end
end
function rule6(v,i,dec,j,c)
    eq = dec[i][2]
    if v[1]==eq[1][1]
        push!(e,(c[1][1],string("∀",im(eq[1],v))))
        find(nap(eq[1],v,c),i,dec,c)
        if eq[end][1]!="true"
            find(ap(eq[end],v,c),i,dec,c)
        else
            push!(e,(c[1][1],'T'))
        end
    else
        push!(e,(c[1][1],'?'))
    end
end
function rule7(v,i,dec,j,c)
    eq = dec[i][2]
    if v[1]==n(eq[1][1])
        push!(e,(c[1][1],string("∀",im(eq[1],v))))
        find(ap(eq[1],v,c),i,dec,c)
        if eq[end][1]!="true"
            find(ap(eq[end],v,c),i,dec,c)
        else
            push!(e,(c[1][1],'T'))
        end
    end
    if v[1]==eq[1][1]
        push!(e,(c[1][1],string("∀",im(eq[1],v))))
        find(nap(eq[1],v,c),i,dec,c)
        if eq[end][1]!="true"
            find(ap(eq[end],v,c),i,dec,c)
        else
            push!(e,(c[1][1],'T'))
        end
    end
    if v[1]==eq[end][1] #|| v[1]==n(eq[end][1])
        push!(e,(c[1][1],string("∀",im(eq[1],v))))
        find(ap(eq[1],v,c),i,dec,c)
        find(nap(eq[1],v,c),i,dec,c)
    end
end
function mou(v,i,dec)
    global e = []
    global nbc = 1
    dec[i][1](v,i,dec,1,[("1",[],i)])
    find(v,i,dec,[("1",[],i)])
    printe()
end

# Décompositions
alldiff = [(rule1,[("X",id),("b",id)]), 
(rule4,[("nb",i->[i[1]*'\'',i[2]]),("true",id)])]

alleq   = [(rule2,[("X",id),("b",id)]),
(rule4,[("b",i->[i[1]*"'",i[end],"∃"*i[1]*"'"]),("nb",i->[i[1]*"'",i[end],"∃"*i[1]*"'"]),("true",id)])]

alleq2  = [(rule2,[("X",id),("b",id)]),
(rule3,[("b",i->[i[1]*"'",i[end]]),("b1",id)]),
(rule3,[("nb",i->[i[1]*"'",i[end]]),("b2",id)]),
(rule4,[("b1",id),("b2",id),("true",id)])]

incr    = [(rule2,[("X",id),("b",id)]), 
(rule4,[("b",i->[i[1]*"+1",i[2]]),("nb",i->[i[1]*"-1",i[2]]),("true",id)])]

atmost  = [(rule1,[("X",id),("b",id)]), 
(rule5,[("b",i->[i[1]*'\'',i[2]]),("true",id)])]

nvalue  = [(rule1,[("X",id),("b",id)]), 
(rule4,[("b",i->[i[1]*'\'',i[2]]),("b2",id)]),
(rule7,[("b2",i->[i[1],i[2]*'\'']),("true",id)])]

cumu    = [(rule2,[("X",id),("b",id)]), 
(rule3,[("b",i->[i[1],i[2]*"-d"*i[1]]),("nb",i->[i[1],i[2]*"+d"*i[1]]),("b2",id)]),
(rule5,[("b2",i->[i[1]*'\'',i[2]]),("true",id)])]

gcc     = [(rule1,[("X",id),("b",id)]),
(rule7,[("b",i->[i[1]*"'",i[2]]),("true",id)])]

allbc   = [(rule2,[("X",id),("b",id)]),
(rule3,[("b",i->[i[1],i[2]*'2']),("nb",i->[i[1],i[2]*'2']),("b2",i->[i[1],i[2]])]),
(rule7,[("b2",i->[i[1]*'\'',i[2]]),("b3",id)]),
(rule4,[("nb3",i->[i[1],i[2]]),("b2",i->[i[1],i[2]]),("b",i->[i[1],i[2]*"2"]),("nb",i->[i[1],i[2]*"1"]),("true",id)])
]

element = [(rule1,[("X",id),("b",id)]),(rule1,[("I",id),("bi",id)]),(rule1,[("V",id),("bv",id)]),
(rule4,[("b",i->["i","t"]),("nbv",i->["t"]),("nbi",i->["i"]),("true",id)]),
(rule4,[("nb",i->["i","t"]),("bv",i->["t"]),("nbi",i->["i"]),("true",id)])
]

range   = [(rule1,[("X",id),("b",id)]),
(rule7,[("b",i->[i[1],i[2]*'\'']),("b1",id)]),
(rule6,[("b",i->[i[1]*'\'',i[2]]),("b2",id)]),
(rule4,[("b1",id),("b2",id),("true",id)])
]

roots   = [(rule1,[("X",id),("b",id)]),
#(rule7,[("b",i->[i[1],i[2]*'\'']),("true",id)]),
(rule7,[("b",i->[i[1],i[2]*'\'']),("true",id)])]


# Tests
global e = []
piv = ("b",["i","t"])
npiv=("nb",["i","t"])

println("\n --AllDifferent--")
mou( piv,1,alldiff)
mou(npiv,1,alldiff)
println("\n --AllEqual--")
mou( piv,1,alleq)
mou(npiv,1,alleq)
println("\n --AllEqual2--")
mou( piv,1,alleq2)
mou(npiv,1,alleq2)
println("\n --Increasing--")
mou( piv,1,incr)
mou(npiv,1,incr)
println("\n --AtMost--")
mou( piv,1,atmost)
mou(npiv,1,atmost)
println("\n --NValue--")
mou( piv,1,nvalue)
mou(npiv,1,nvalue)
println("\n --Cumulative--")
mou( piv,1,cumu)
mou(npiv,1,cumu)
println("\n --Gcc--")
mou( piv,1,gcc)
mou(npiv,1,gcc)
println("\n --AllDiffBC?--")
#mou( piv,1,allbc)
mou(npiv,1,allbc)
println("\n --Element--")
mou( piv,1,element)
mou(npiv,1,element)
mou(("bi",["i"]),2,element)
mou(("nbi",["i"]),2,element)
mou(("bv",["t"]),3,element)
mou(("nbv",["t"]),3,element)
println("\n --Range--")
mou( piv,1,range)
mou(npiv,1,range)
println("\n --Roots--")
mou( piv,1,roots)
mou(npiv,1,roots)

# symboles
# ∈ ∉ ≤ ≥ ∧ ∨ ≠ ∀ ∃ || []

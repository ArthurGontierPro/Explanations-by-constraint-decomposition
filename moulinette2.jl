function printe(verbose=false)
    print(" ",e[1]," <- ")
    for i in 2:size(e,1)
        if !verbose && (e[i] in ['T','F','?'] || e[i] in e[1:i-1])
        else
            print(e[i],"   ")
        end
    end
    println()
end
function id(x)
    return x
end
function n(var)
    return if var[1]=='n' var[2:end] else string('n',var) end
end
function ap(te,v)
    return (te[1],te[2](v[2]),te[3](v[3]))
end
function nap(te,v)
    return (n(te[1]),te[2](v[2]),te[3](v[3]))
end
function find(v,prec,dec)#;printe(true)
    for i in 1:size(dec,1)
        for j in 1:size(dec[i][2],1)
            if (v[1]==dec[i][2][j][1]||n(v[1])==dec[i][2][j][1])&&i!=prec
                dec[i][1](v,i,dec,j)
            end
        end
    end
end
function rule1(v,i,dec,j)
    eq = dec[i][2]
    if v[1]==eq[1][1]
        find(ap(eq[2],v),i,dec)
    elseif v[1]==n(eq[1][1])
        find(nap(eq[2],v),i,dec)
    elseif v[1]==eq[end][1]
        push!(e,string(eq[1][1],v[2],'=',v[3]))
    else
        push!(e,string(eq[1][1],v[2],'≠',v[3]))
    end
end
function rule2(v,i,dec,j)
    eq = dec[i][2]
    if v[1]==eq[1][1]
        find(ap(eq[2],v),i,dec)
    elseif v[1]==n(eq[1][1])
        find(nap(eq[2],v),i,dec)
    elseif v[1]==eq[end][1]
        push!(e,string(eq[1][1],v[2],'≥',v[3]))
    else
        push!(e,string(eq[1][1],v[2],'<',v[3]))
    end
end
function rule3(v,i,dec,j)
    eq = dec[i][2]
    if j<size(eq,1)
        if v[1]==eq[j][1]
            if eq[end][1]!="true"
                find(ap(eq[end],v),i,dec)
            else
                push!(e,'T')
            end
        end
        if v[1]==n(eq[j][1])
            if eq[end][1]!="true"
                find(nap(eq[end],v),i,dec)
                for jj in 1:size(eq,1)-1
                    if j != jj
                        find(ap(eq[jj],v),i,dec)
                    end
                end
            else
                push!(e,'F')
            end
        end
    else
        if v[1]==eq[end][1]
            for jj in 1:size(eq,1)-1
                find(ap(eq[jj],v),i,dec)
            end
        end
        if v[1]==n(eq[end][1])
            for jj in 1:size(eq,1)-1
                find(nap(eq[jj],v),i,dec)
            end
        end
    end
end
function rule4(v,i,dec,j)
    eq = dec[i][2]
    if j<size(eq,1)
        if v[1]==eq[j][1]
            for jj in 1:size(eq,1)-1
                if j != jj
                    find(nap(eq[jj],v),i,dec)
                end
            end
            if eq[end][1]!="true"
                find(ap(eq[end],v),i,dec)
            else
                push!(e,'T')
            end
        end
        if v[1]==n(eq[j][1])
            if eq[end][1]!="true"
                find(nap(eq[end],v),i,dec)
            else
                push!(e,'?')
            end
        end
    else
        if v[1]==eq[end][1]
            for jj in 1:size(eq,1)-1
                find(ap(eq[jj],v),i,dec)#il existe?
            end
        end
        if v[1]==n(eq[end][1])
            for jj in 1:size(eq,1)-1
                find(nap(eq[jj],v),i,dec)
            end
        end
    end
end
function rule5(v,i,dec,j)
    eq = dec[i][2]
    if v[1]==n(eq[1][1])
        find(ap(eq[1],v),i,dec)
        if eq[end][1]!="true"
            find(ap(eq[end],v),i,dec)
        else
            push!(e,'T')
        end
    else
        push!(e,'?')
    end
end
function rule6(v,i,dec,j)
    eq = dec[i][2]
    if v[1]==eq[1][1]
        find(nap(eq[1],v),i,dec)
        if eq[end][1]!="true"
            find(ap(eq[end],v),i,dec)
        else
            push!(e,'T')
        end
    else
        push!(e,'?')
    end
end
function rule7(v,i,dec,j)
    eq = dec[i][2]
    if v[1]==n(eq[1][1])
        find(ap(eq[1],v),i,dec)
        if eq[end][1]!="true"
            find(nap(eq[end],v),i,dec)
        else
            push!(e,'T')
        end
    end
    if v[1]==eq[1][1]
        find(ap(eq[1],v),i,dec)
        if eq[end][1]!="true"
            find(nap(eq[end],v),i,dec)
        else
            push!(e,'T')
        end
    end
    if v[1]==eq[end][1] || v[1]==n(eq[end][1])
        find(ap(eq[1],v),i,dec)
        find(nap(eq[1],v),i,dec)
    end
end
function mou(v,i,dec)
    global e = []
    dec[i][1](v,i,dec,1)
    find(v,i,dec)
    printe()
end

# Décompositions
alldiff = [(rule1,[("X",id,id),("b",id,id)]), 
(rule4,[("nb",i->i*'\'',id),("nb",i->i*'\'',id),("true",id,id)])]

alleq   = [(rule2,[("X",id,id),("b",id,id)]), 
(rule4,[("nb",i->i*'\'',id),("b",i->i*'\'',id),("true",id,id)])]

incr    = [(rule2,[("X",id,id),("b",id,id)]), 
(rule4,[("b",i->i*"+1",id),("nb",i->i*"-1",id),("true",id,id)])]

atmost  = [(rule1,[("X",id,id),("b",id,id)]), 
(rule5,[("b",i->i*'\'',id),("true",id,id)])]

nvalue  = [(rule1,[("X",id,id),("b",id,id)]), 
(rule4,[("b",i->i*'\'',id),("b",i->i*'\'',id),("b2",id,id)]),
(rule7,[("b2",id,t->t*'\''),("true",id,id)])]

cumu    = [(rule2,[("X",id,id),("b",id,id)]), 
(rule3,[("b",id,t->t*"-di"),("nb",id,t->t*"+di"),("b2",id,id)]),
(rule5,[("b2",i->i*'\'',id),("true",id,id)])]

allbc   = [(rule2,[("X",id,id),("b",id,id)]), 
#(rule3,[("b",id,t->t*"'"),("nb",id,t->t*"'"),("b2",id,t->"t,t'")]),
#(rule7,[("b2",i->i*'\'',id),("b3",id,id)]),
(rule4,[("b",i->i*'?',t->t*"1"),("nb",i->i*'?',t->t*"2"),("nb3",i->i*'\'',id),("true",id,id)])]

# Tests
global e = []
piv = ("b","i","t")
npiv=("nb","i","t")

println("\n --AllDifferent--")
mou( piv,1,alldiff)
mou(npiv,1,alldiff)
println("\n --AllEqual--")
mou( piv,1,alleq)
mou(npiv,1,alleq)
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
println("\n --AllDiffBC--")
mou( piv,1,allbc)
#mou(npiv,1,allbc)

# Sortie
# julia> include("moulinette 2.jl")
# --AllDifferent--
# Xi=t <- 
# Xi≠t <- Xi'=t   

# --AllEqual--
# Xi≥t <- Xi'≥t   
# Xi<t <- Xi'<t   

# --Increasing--
# Xi≥t <- Xi-1≥t   
# Xi<t <- Xi+1<t   

# --AtMost--
# Xi=t <- 
# Xi≠t <- Xi'=t   

# --NValue--
# Xi=t <- Xi'≠t   Xi'=t'   
# Xi≠t <- Xi'=t'   

# --Cumulative--
# Xi≥t <- Xi'≥t-di   Xi'<t+di   Xi≥t-di   
# Xi<t <- Xi'≥t-di   Xi'<t+di   Xi<t+di   

# --AllDiffBC--
# Xi≥t <- Xi?≥t2   

# symboles
# ∈ ∉ ≤ ≥ ∧ ∨ ≠ || []

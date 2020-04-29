function printm(m)
    for i in 1:size(m,1)      
	for j in 1:size(m,2)
	    print(m[i,j],"  ")
	end
	println()
    end
end

function printpiv(p)
    return string("X",p[2],if p[1]==1 " ≥ " elseif p[1]==2 " ≤ " else " ≠ " end,p[3])
end

function mou(dec,piv)#v3 : simplement trouver les variables qui interviènent mais c naze
    e = dec[1][piv[1]](piv)
    s = '('
    for i in 1:size(e,1)
        s=string(s,dec[2][piv[1]](piv,e[i]))
    end
    return string(s,printpiv(piv),")")
end

# symboles
# ∈ ∉ ≤ ≥ ∧ ∨ ≠  []

cumul = ((
p->findall(x->x==1,[X[i][2]<=p[3]-1&&p[3]-1<X[i][1]+d[i] for i in 1:size(X,1)]),
p->findall(x->x==1,[X[i][2]<=p[3]+d[p[2]]&&p[3]+d[p[2]]<X[i][1]+d[i] for i in 1:size(X,1)]),
p->"Undef"),(
(p,e)->string("S",e,"∉[",max(0,p[3]-1-d[e]),",",p[3]-1,"] ∨ "),
(p,e)->string("S",e,"∉[",max(0,p[3]+d[p[2]]-d[e]),",",p[3]+d[p[2]],"] ∨ "),
(p,e)->"Undef"))

alleq = ((
p->findall(x->x[1]==p[3],X),
p->findall(x->x[2]==p[3],X),p->"Undef"),(
(p,e)->string("x",e,"<",p[3]," ∨ "),
(p,e)->string("x",e,">",p[3]," ∨ "),(p,e)->"Undef"))


# Instances
global X = [(1,1),(1,1),(3,10),(3,8),(5,10),(8,11),(5,10)]
global d = [4,7,3,8,6,3,2]
global c = 2

pivot = (1,3,4)
println(mou(cumul,pivot))
pivot = (1,6,11)
println(mou(cumul,pivot))
pivot = (2,7,8)
println(mou(cumul,pivot))

global X = [(1,8),(3,10),(3,8)]
pivot = (1,1,3)
println(mou(alleq,pivot))
pivot = (2,2,8)
println(mou(alleq,pivot))


#=Old
function printpiv(p)
    return string("S",p[2],if p[1] " ≥ " else " ≤ " end,p[3])
end
function printpiv2(p)
    return string("x",p[2],if p[1] " ≥ " else " ≤ " end,p[3])
end

function computeb(t)
    b = zeros(Int,size(d,1))
    for i in 1:6
	if s[i][2] <= t && t <s[i][1]+d[i]
	    b[i]=1
	end
    end
    # println(b)
    return b
end
function mou(p)
    if p[1] t = p[3]-1 else t = p[3]+d[p[2]] end
    b = computeb(t)
    e = findall(x->x==1,b)
    s = "("
    if size(e,1)==c
	for i in 1:size(e,1)
	    s=string(s,"S",e[i],"∉[",max(0,t-d[e[i]]),",",t,"] ∨ ")
	end
    end
    return string(s,printpiv(p),")")
end
function mou2(p)
    s = "("
    t = p[3]
    if p[1] 
        for i in 1:size(x,1)
            if x[i][1] == t
                s=string(s,"x",i,"<",t," ∨ ")
            end
        end
    else
        for i in 1:size(x,1)
            if x[i][2] == t
                s=string(s,"x",i,">",t," ∨ ")
            end
        end        
    end
    return string(s,printpiv2(p),")")
end

# Sortie 
# julia> include("moulinette.jl")
# (S1∉[0,3] ∨ S2∉[0,3] ∨ S3 ≥ 4)
# (S4∉[2,10] ∨ S5∉[4,10] ∨ S6 ≥ 11)
# (S4∉[2,10] ∨ S5∉[4,10] ∨ S7 ≤ 8)
# (x2<3 ∨ x3<3 ∨ x1 ≥ 3)
# (x1>8 ∨ x3>8 ∨ X2 ≤ 8)

=#

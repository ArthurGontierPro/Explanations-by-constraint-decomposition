function ap(rr,prefix,r,suffix)
    for i in prefix
        for ii in r
            for iii in suffix
                push!(rr,(i*ii[1]*iii,i*ii[2]*iii))
            end
        end
    end
    return rr
end
function main()
    r=[#types
       ("name","var_name"),
       ("ind","ind_name"),
       ("var","event_var"),
       ("car","decomp_var"),
       ("set","ind_set"),
       ("cst","ind_const"),
       ("sym","ind_symbols"),
       ("iop","ind_modifs"),
       ("lou","index"),
       ("lit","leaf"),
       ("arb","tree"),
       ("consi","consistancy"),
       ("ctr","decomp_ctr")]
    prefix = ["type ","of ",':','*',"print","->"]
    suffix = [' ',')','(','^','*',';',"->","\n"]
    rr = []
    ap(rr,prefix,r,suffix)
    r=[#champs de types
       ("ind","ind_name"),
       ("opl","ind_modifs_list"),
       ("s","var_sign"),
       ("cs","dec_var_sign"),
       ("n","var_name"),
       ("cn","dec_var_name"),
       ("i","index_list"),
       ("fid","index_propagate"),
       ("fau","index_update"),
       ("r","explenation_rule"),
       ("cvl","dec_var_list")]
    prefix = ['{',"{ ",';',"; "]
    suffix = [':','=']
    ap(rr,prefix,r,suffix)
    prefix = ['.']
    suffix = [' ','^',',',')','=']
    ap(rr,prefix,r,suffix)
    r=[#fonctions
       ("var","make_event_var"),
       ("car","make_decomp_var"),
       ("ctr","make_decomp_ctr"),
       ("ind","make_index")]
    prefix = ["let ",'(',' ','=',';','[']
    suffix = [' ']
    ap(rr,prefix,r,suffix)
    r=rr
    nr = size(r,1)
    file1 = open("moulinette.ml", "r")
    file2 = open("moulinetteverbose.ml", "w")
    line = readline(file1)*' '
    while !eof(file1)
        for i in 1:nr
            line=replace(line,r[i][1]=>r[i][2])
        end
        write(file2, line * "\n")
        line = readline(file1)*' '
    end
    close(file1)
    close(file2)
end

main()

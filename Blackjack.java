import java.util.Random;

public class Blackjack {
    enum Carta {
        AT,DOST,TREST,CUATROT,CINCOT,SEIST,SIETET,OCHOT,NUEVET,DIEZT,JT,QT,KT,ET,
        AC,DOSC,TRESC,CUATROC,CINCOC,SEISC,SIETEC,OCHOC,NUEVEC,DIEZC,JC,QC,KC,EC,
        AD,DOSD,TRESD,CUATROD,CINCOD,SEISD,SIETED,OCHOD,NUEVED,DIEZD,JD,QD,KD,ED,
        AP,DOSP,TRESP,CUATROP,CINCOP,SEISP,SIETEP,OCHOP,NUEVEP,DIEZP,JP,QP,KP,EP;
    }        
    static Carta darCarta(Carta[] a) {
        Random carta = new Random();
        int n = carta.nextInt(56);
        return a[n];
    }

    public static void main(String[] args) {
        Carta mazo[] = Carta.values();
        Carta x = darCarta(mazo);
        System.out.println(x);
    }
}

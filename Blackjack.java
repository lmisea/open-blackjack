import java.io.Console;
import java.util.Random;

public class Blackjack {
    // Creación de todas las posibles cartas

    enum Carta {
        AS_PICAS, DOS_PICAS, TRES_PICAS, CUATRO_PICAS,
        CINCO_PICAS, SEIS_PICAS, SIETE_PICAS, OCHO_PICAS,
        NUEVE_PICAS, DIEZ_PICAS, J_PICAS, Q_PICAS,
        K_PICAS, COMODÍN_PICAS, AS_DIAMANTE, DOS_DIAMANTE,
        TRES_DIAMANTE, CUATRO_DIAMANTE, CINCO_DIAMANTE, SEIS_DIAMANTE,
        SIETE_DIAMANTE, OCHO_DIAMANTE, NUEVE_DIAMANTE, DIEZ_DIAMANTE,
        J_DIAMANTE, Q_DIAMANTE, K_DIAMANTE, COMODÍN_DIAMANTE,
        AS_TREBOL, DOS_TREBOL, TRES_TREBOL, CUATRO_TREBOL,
        CINCO_TREBOL, SEIS_TREBOL, SIETE_TREBOL, OCHO_TREBOL,
        NUEVE_TREBOL, DIEZ_TREBOL, J_TREBOL, Q_TREBOL,
        K_TREBOL, COMODÍN_TREBOL, AS_CORAZON, DOS_CORAZON,
        TRES_CORAZON, CUATRO_CORAZON, CINCO_CORAZON, SEIS_CORAZON,
        SIETE_CORAZON, OCHO_CORAZON, NUEVE_CORAZON, DIEZ_CORAZON,
        J_CORAZON, Q_CORAZON, K_CORAZON, COMODÍN_CORAZON;

        private Carta() {
        }
    }

    // Métodos para obtener información de las cartas que se repartan aleatoriamente

    public static String obtenerPaloCarta(Carta carta) {
        if (carta.ordinal() <= 13)
            return "Picas";
        else if (carta.ordinal() <= 27)
            return "Diamantes";
        else if (carta.ordinal() <= 41)
            return "Treboles";
        else
            return "Corazones";
    }

    public static int obtenerValorCarta(Carta carta) {
        if (carta.ordinal() % 14 <= 9)
            return (carta.ordinal() % 14) + 1;
        else if (carta.ordinal() % 14 <= 12)
            return 10;
        else
            return 11;
    }

    public static String obtenerNombreCarta(Carta carta) {
        if (carta.ordinal() % 14 == 0)
            return "A";
        else if (carta.ordinal() % 14 <= 9)
            return Integer.toString(obtenerValorCarta(carta));
        else if (carta.ordinal() % 14 == 10)
            return "J";
        else if (carta.ordinal() % 14 == 11)
            return "Q";
        else if (carta.ordinal() % 14 == 12)
            return "K";
        else
            return "Joker";
    }

    // Función Repartir una Carta

    public static Carta darCarta(Carta[] baraja) {
        Random carta = new Random();
        int aleatorio = carta.nextInt(56);
        return baraja[aleatorio];
    }

    // Función Obtener monto de la apuesta

    public static int obtenerApuesta(int x) {
        Console con = System.console();
        int i = 0;
        int apuesta = Integer.parseInt(con.readLine("Para empezar la partida ingresa el monto ha apostar: "));
        while (apuesta > x || apuesta < 10) {
            apuesta = Integer.parseInt(con.readLine("Cantidad errónea, por favor ingrese otro monto: "));
            i++;
            if (i == 5) {
                apuesta = 10;
            }
        }
        return apuesta;
    }

    // Función Determinar el valor de una mano

    // public static int valorMano(Carta[] manoJugador, int numCartasMano, int
    // puntosMano) {
    // int i = 0;
    // while (i < numCartasMano) {
    // puntosMano = manoJugador[i].valor + puntosMano;
    // i++;
    // }
    // return puntosMano;
    // }

    public static void main(String[] args) {
        Carta mazo[] = new Carta[] {
                Carta.AS_PICAS, Carta.DOS_PICAS, Carta.TRES_PICAS, Carta.CUATRO_PICAS,
                Carta.CINCO_PICAS, Carta.SEIS_PICAS, Carta.SIETE_PICAS, Carta.OCHO_PICAS,
                Carta.NUEVE_PICAS, Carta.DIEZ_PICAS, Carta.J_PICAS, Carta.Q_PICAS,
                Carta.K_PICAS, Carta.COMODÍN_PICAS, Carta.AS_DIAMANTE, Carta.DOS_DIAMANTE,
                Carta.TRES_DIAMANTE, Carta.CUATRO_DIAMANTE, Carta.CINCO_DIAMANTE, Carta.SEIS_DIAMANTE,
                Carta.SIETE_DIAMANTE, Carta.OCHO_DIAMANTE, Carta.NUEVE_DIAMANTE, Carta.DIEZ_DIAMANTE,
                Carta.J_DIAMANTE, Carta.Q_DIAMANTE, Carta.K_DIAMANTE, Carta.COMODÍN_DIAMANTE,
                Carta.AS_TREBOL, Carta.DOS_TREBOL, Carta.TRES_TREBOL, Carta.CUATRO_TREBOL,
                Carta.CINCO_TREBOL, Carta.SEIS_TREBOL, Carta.SIETE_TREBOL, Carta.OCHO_TREBOL,
                Carta.NUEVE_TREBOL, Carta.DIEZ_TREBOL, Carta.J_TREBOL, Carta.Q_TREBOL,
                Carta.K_TREBOL, Carta.COMODÍN_TREBOL, Carta.AS_CORAZON, Carta.DOS_CORAZON,
                Carta.TRES_CORAZON, Carta.CUATRO_CORAZON, Carta.CINCO_CORAZON, Carta.SEIS_CORAZON,
                Carta.SIETE_CORAZON, Carta.OCHO_CORAZON, Carta.NUEVE_CORAZON, Carta.DIEZ_CORAZON,
                Carta.J_CORAZON, Carta.Q_CORAZON, Carta.K_CORAZON, Carta.COMODÍN_CORAZON };
        Carta jugador[] = new Carta[21];
        Carta crupier[] = new Carta[21];
        int crédito = 100;

        Console con = System.console();
        String name = con.readLine("Ingrese su nombre: ");
        System.out.println("Es un placer tenerte aquí " + name);
        Carta cartaAleatoria = darCarta(mazo);
        System.out.println(cartaAleatoria);
        System.out.println(obtenerPaloCarta(cartaAleatoria));
        System.out.println(obtenerValorCarta(cartaAleatoria));
        System.out.println(obtenerNombreCarta(cartaAleatoria));

        // while (crédito >= 10) {
        // int i = 0;
        // int j = 2;
        // int apuesta = obtenerApuesta(crédito);
        // while (i < 2) {
        // jugador[i] = darCarta(mazo);
        // crupier[i] = darCarta(mazo);
        // i++;
        // }
        // int valorJugador = valorMano(jugador, j, 0);
        // int valorCrupier = valorMano(crupier, j, 0);
        // System.out.println(valorJugador);
        // System.out.println(valorCrupier);
        // System.out.println(crupier[0].valor);

        // break;
        // }
        System.out.println("El juego se ha terminado");
    }
}

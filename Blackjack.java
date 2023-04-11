import java.io.Console;
import java.util.Random;
import java.util.Scanner;
import java.awt.Font;

public class Blackjack {
    // Creacion de un enum con todas las posibles cartas
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

    // Metodos para obtener informacion de las cartas que se repartan aleatoriamente

    /**
	 * Metodo con el que se obtendra el palo de cualquier carta
     * perteneciente al enum Carta
     */
    //@ requires carta != null;
    //@ ensures \result == "Picas" || \result == "Diamantes" || \result == "Treboles" || \result == "Corazones";
    public static /*@ pure @*/ String obtenerPaloCarta(Carta carta) {
        if (carta.ordinal() <= 13)
            return "Picas";
        else if (carta.ordinal() <= 27)
            return "Diamantes";
        else if (carta.ordinal() <= 41)
            return "Treboles";
        else
            return "Corazones";
    }

    /**
	 * Metodo con el que se obtendra el valor de cualquier carta
     * perteneciente al enum Carta
     */
    //@ requires carta != null;
    //@ ensures 0 < \result <= 11;
    public static /*@ pure @*/ int obtenerValorCarta(Carta carta) {
        if (carta.ordinal() % 14 <= 9)
            return (carta.ordinal() % 14) + 1;
        else if (carta.ordinal() % 14 <= 12)
            return 10;
        else
            return 11;
    }

    /**
	 * Metodo con el que se obtendra el nombre de cualquier carta perteneciente
     * al enum Carta. El nombre de una carta es lo que va en sus esquinas.
     */
    //@ requires carta != null;
    //@ ensures \result.equals("A") || \result.equals("J") || \result.equals("Q") || \result.equals("K") || \result.equals("Joker") || 2 <= Integer.parseInt(\result) <= 10;
    public static /*@ pure @*/ String obtenerNombreCarta(Carta carta) {
        if (carta.ordinal() % 14 == 0)
            return "A";
        else if (carta.ordinal() % 14 <= 9)
            return Integer.toString((carta.ordinal() % 14) + 1);
        else if (carta.ordinal() % 14 == 10)
            return "J";
        else if (carta.ordinal() % 14 == 11)
            return "Q";
        else if (carta.ordinal() % 14 == 12)
            return "K";
        else
            return "Joker";
    }

    /**
	 * Metodo con el que se repartira una de las 56 cartas al azar
     */
    //@ requires baraja.length == 56;
    //@ ensures (\exists int i; 0 <= i && i < baraja.length; \result == baraja[i]);
    public static /*@ pure @*/ Carta darCarta(Carta[] baraja) {
        Random carta = new Random();
        int aleatorio = carta.nextInt(56);
        //@ assert aleatorio >= 0 && aleatorio < 56 ;
        return baraja[aleatorio];
    }

    /**
	 * Metodo que permite registrar el monto de la apuesta del jugador
     * para la mano actual
     */
    //@ requires credito >= 10 && credito < Integer.MAX_VALUE / 2;
    //@ requires nombre.length() > 0;
    //@ ensures 10 <= \result || \result <= credito;
    public static /*@ non_null */ int obtenerApuesta(int credito, String nombre) {
        int i = 0;
        Scanner entrada = new Scanner(System.in);
        System.out.print(nombre + ", por favor ingresa el monto que te gustaría apostar en esta mano: ");
        int apuesta = entrada.nextInt();

        //@ maintaining 0 <= i <= 4;
        //@ maintaining (\forall int k; 0 <= k && k < i; apuesta > credito || apuesta < 10 || apuesta <= credito || apuesta >= 10 );
        //@ decreases 4 - i;
        while (i < 4) {
            if (i == 3) {
                System.out.println("Se le ha establecido la apuesta minima : 10");
                apuesta = 10;
                break;
            } else if (apuesta > credito || apuesta < 10) {
                System.out.println("Cantidad invalida. La apuesta debe ser mayor igual a 10 y menor igual al numero de creditos.");
                System.out.print(nombre + ", por favor ingresa otro monto que desees apostar: ");
                apuesta = entrada.nextInt();
                i++;
            } else if (apuesta <= credito && apuesta >= 10) {
                break;
            }
        }
		System.out.println("Siempre que apuestes, se te va descontar la apuesta de tus creditos actuales mientras se este jugando la mano.");
		System.out.println("Si ganas se te devuelve la apuesta junto con su ganacia.");
		System.out.println("Si pierdes no se te devolvera la apuesta y terminaras perdiendo dinero.");
        return apuesta;
    }


    /**
	 * Metodo que permite calcular el valor de la suma de las cartas de una mano
     */
    //@ requires 0 <= numCartasMano <= manoJugador.length;
    //@ requires 0 <= puntosMano < Integer.MAX_VALUE;
    //@ ensures 2 <= \result || \result < 31 || \result == puntosMano ;
    public static /*@ pure @*/ int valorMano(/*@ non_null */ Carta /*@ non_null */[] manoJugador, int numCartasMano, int puntosMano) {
        puntosMano = 0;

        //@ maintaining 0 <= numCartasMano <= manoJugador.length;
        //@ maintaining (\forall int k; 0 <= k && k < numCartasMano; manoJugador[k].ordinal() % 14 >= 1 || manoJugador[k].ordinal() % 14 <= 11);
        //@ decreases numCartasMano;
        while (numCartasMano != 0) {
            numCartasMano -= 1;
            //@ assume 0 <= numCartasMano <= 21;
            //@ assume 0 <= puntosMano < 31;
            if (manoJugador[numCartasMano].ordinal() % 14 <= 9)
                puntosMano = (manoJugador[numCartasMano].ordinal() % 14) + 1 + puntosMano;
            else if (manoJugador[numCartasMano].ordinal() % 14 <= 12)
                puntosMano = 10 + puntosMano ;
            else
                puntosMano = 11 + puntosMano;
            //@ assert puntosMano >= 2 || puntosMano <= 31;
        }
        //@ assert puntosMano >= 2 || puntosMano <= 31;
        return puntosMano;
    }

	public static int ganancia(int apuesta, int credito, int indicador) {
		// Ganancia del jugador 	
		if (indicador == 1){
			// Si hizo blackjack, relacion 3:2
			credito = apuesta + (int) apuesta * 3/2;
			return credito;
		} else if (indicador == 2) {
			// Gana con una relacion 1:1
			credito = apuesta*2;
			return credito;
		} else if (indicador == 3){
			// Empate y se le devuelve el dinero
			credito = credito + apuesta;
			return credito;
		}else 
			return credito;
	}

	public static int opciones(String nombre) {
		// Opciones del jugador
		Scanner entrada = new Scanner(System.in);
		System.out.println(nombre+ " estas son tus opciones: ");
		System.out.println("(1) Recibir una carta");
		System.out.println("(2) Plantarse");
		System.out.println("(3) Doblar el monto de la apuesta");
		System.out.println("(4) Salir del juego");
		System.out.print("Opcion: ");
		int opcion = entrada.nextInt();
		while (opcion > 4 && opcion < 1) {
			System.out.print(nombre +" has elegido una opcion erronea");
			System.out.print("Por favor escoga una opcion :");
			opcion = entrada.nextInt();
		}
		return opcion;
	}

	public static int mensajeJugador(int puntosJugador, int puntosCrupier ) {
		// Mensaje para el jugador en cada caso
		if (puntosJugador > 21){
			System.out.println("Haz perdido la partida.");
			System.out.println("Tu puntaje es mayor que 21.");
			return 1;
		} else if (puntosJugador == puntosCrupier) {
			System.out.println("Ha ocurrido un empate");
			System.out.println("Tienes los mismo puntos que el crupier");
			return 2;
		} else if (puntosJugador == 21) {
			System.out.println("¡Hiciste BLACKJACK!");
			System.out.println("Tu puntaje es de 21.");
			System.out.println("Haz ganado la partida.");
			return 3;
			
		}else
			return 4;
	}
	public static int mensajeCrupier(int puntosCrupier ) {
		// Mensaje del crupier si se paso del limite
		if (puntosCrupier > 21){
			System.out.println("El puntaje del crupier es mayor que 21");
			System.out.println("Haz ganado la partida.");
			return 1;
		}else
			return 2;
	}

	public static int decision(int puntosJugador, int puntosCrupier ) {
		// Mensaje para el jugador en cada caso
		if (puntosJugador < puntosCrupier){
			System.out.println("Haz perdido la partida.");
			return 1;
		}else if (puntosJugador > puntosCrupier) {
			System.out.println("Haz ganado la partida.");
			return 2;
		} else if (puntosJugador == puntosCrupier) {
			System.out.println("Ha ocurrido un empate");
			return 3;
		} else
			return 4;
	}

	public static int doblarApuesta(int puntosJugador, int puntosCrupier, int apuesta, int credito) {
		// Verificar si se puede doblar la apuesta
		if ((puntosJugador == 9 || puntosJugador == 10 || puntosJugador == 11) && apuesta*2 < credito) {
			// Doblarla
			apuesta = apuesta*2;
			return apuesta;
		}else { 
			// Mensaje de error al no cumplir verificacion
			System.out.println("Para doblar necesita que la suma de sus puntos sea 9,10 o 11 y tener suficiente credito");
			System.out.println("Como no cumple el requisito no puede doblar la apuesta.");
			return apuesta;
		}
	}

	public static int operacionCredito(int apuesta, int credito, int indicador) {
		if (indicador == 1){
			// Restar credito
			credito = credito - apuesta;
			return credito;
		}else if (indicador == 2){
			// Sumar credito
			credito = credito + apuesta;
			return credito;	
		}else if (indicador == 3){
			// Restar credito al decidir apostar el doble
			credito = credito - apuesta/2;
			return credito;
		} else
			return credito;
	}

	/**
	 * Metodo con el que se mostrara graficamente las cartas visibles que vayan
	 * apareciendo en la mano del jugador y en la del crupier
	 */
	//@ requires mesa != null;
	//@ requires 0 < mesa.XMAX < Integer.MAX_VALUE;
	//@ requires 0 < mesa.YMAX < Integer.MAX_VALUE;
	//@ requires 0 <= (posXdeCarta + 4) < Integer.MAX_VALUE;
	//@ requires 0 <= (posYdeCarta + 5) < Integer.MAX_VALUE;
	//@ requires 30 <= alturaCarta <= 10000;
	//@ requires 30 <= anchoCarta <= 10000;
	//@ requires (posXdeCarta + anchoCarta) < Integer.MAX_VALUE;
	//@ requires (posYdeCarta + alturaCarta) < Integer.MAX_VALUE;
	//@ requires (posXdeCarta + (anchoCarta / 2) + 25) < Integer.MAX_VALUE;
	//@ requires (posYdeCarta + (alturaCarta / 2) + 18) < Integer.MAX_VALUE;
	//@ requires paloCarta.equals("Picas") || paloCarta.equals("Diamantes") || paloCarta.equals("Treboles") || paloCarta.equals("Corazones");
	//@ requires nombreCarta.length() > 0;
	public static void dibujarCartaVisible(MaquinaDeTrazados mesa, int posXdeCarta, int posYdeCarta,
			int alturaCarta, int anchoCarta, String paloCarta, String nombreCarta) {
		// Dibujar el rectángulo externo e interno de la carta
		mesa.dibujarRectanguloLleno(posXdeCarta, posYdeCarta, 72, 108, Colores.WHITE);
		mesa.dibujarRectangulo(posXdeCarta + 4, posYdeCarta + 5, anchoCarta - 10, alturaCarta - 10, Colores.DARK_GRAY);
		Colores color = Colores.BLACK;

		// Dibujar el símbolo de los palos de las cartas
		if (paloCarta.equals("Picas")) {
			// Dibujar el símbolo de Picas
			int[] xPuntos1 = new int[] { posXdeCarta + (anchoCarta / 2) - 12, posXdeCarta + (anchoCarta / 2),
					posXdeCarta + (anchoCarta / 2) + 11, posXdeCarta + (anchoCarta / 2) };
			int[] yPuntos1 = new int[] { posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) - 15,
					posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) + 5 };
			int[] xPuntos2 = new int[] { posXdeCarta + (anchoCarta / 2) - 6, posXdeCarta + (anchoCarta / 2),
					posXdeCarta + (anchoCarta / 2) + 6 };
			int[] yPuntos2 = new int[] { posYdeCarta + (alturaCarta / 2) + 18, posYdeCarta + (alturaCarta / 2) + 12,
					posYdeCarta + (alturaCarta / 2) + 18 };
			mesa.dibujarPoligonoLleno(xPuntos1, yPuntos1, 4, color);
			mesa.dibujarPoligonoLleno(xPuntos2, yPuntos2, 3, color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 15, posYdeCarta + (alturaCarta / 2) - 1, 15, 15,
					color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 1, posYdeCarta + (alturaCarta / 2) - 1, 15, 15,
					color);

		} else if (paloCarta.equals("Diamantes")) {
			// Dibujar el símbolo de Diamantes
			color = Colores.RED;
			int[] xPuntos = new int[] { posXdeCarta + (anchoCarta / 2) - 12, posXdeCarta + (anchoCarta / 2),
					posXdeCarta + (anchoCarta / 2) + 12, posXdeCarta + (anchoCarta / 2) };
			int[] yPuntos = new int[] { posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) - 18,
					posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) + 18 };
			mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 4, color);

		} else if (paloCarta.equals("Treboles")) {
			// Dibujar el símbolo de Treboles
			int[] xPuntos = new int[] { posXdeCarta + (anchoCarta / 2) - 6, posXdeCarta + (anchoCarta / 2),
					posXdeCarta + (anchoCarta / 2) + 6 };
			int[] yPuntos = new int[] { posYdeCarta + (alturaCarta / 2) + 18, posYdeCarta + (alturaCarta / 2) + 12,
					posYdeCarta + (alturaCarta / 2) + 18 };
			mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 3, color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 17, posYdeCarta + (alturaCarta / 2) - 2,
					17, 17, color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 1, posYdeCarta + (alturaCarta / 2) - 2,
					17, 17, color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 9, posYdeCarta + (alturaCarta / 2) - 15,
					17, 17, color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 4, posYdeCarta + (alturaCarta / 2) - 1,
					8, 8, color);

		} else if (paloCarta.equals("Corazones")) {
			// Dibujar el símbolo de Corazones
			color = Colores.RED;
			int[] xPuntos = new int[] { posXdeCarta + (anchoCarta / 2) - 14, posXdeCarta + (anchoCarta / 2),
					posXdeCarta + (anchoCarta / 2) + 14, posXdeCarta + (anchoCarta / 2) };
			int[] yPuntos = new int[] { posYdeCarta + (alturaCarta / 2) + 1, posYdeCarta + (alturaCarta / 2) - 2,
					posYdeCarta + (alturaCarta / 2) + 1, posYdeCarta + (alturaCarta / 2) + 15 };
			mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 4, color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 16, posYdeCarta + (alturaCarta / 2) - 12, 17, 17,
					color);
			mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 2, posYdeCarta + (alturaCarta / 2) - 12, 17, 17,
					color);
		}

		// Escribir el nombre de la carta en las esquinas
		int posXEsqInfIzquierda = posXdeCarta + anchoCarta - 24;
		int posYEsqInfIzquierda = posYdeCarta + alturaCarta - 12;

		mesa.configurarFuente("SansSerif", Font.BOLD, 18);
		mesa.dibujarString(nombreCarta, posXdeCarta + 11, posYdeCarta + 24, color);
		if (nombreCarta.equals("A")) {
			posXEsqInfIzquierda = posXdeCarta + anchoCarta - 26;
			posYEsqInfIzquierda = posYdeCarta + alturaCarta - 10;
		} else if (nombreCarta.equals("10")) {
			posXEsqInfIzquierda = posXdeCarta + anchoCarta - 36;
			posYEsqInfIzquierda = posYdeCarta + alturaCarta - 10;
		} else if (nombreCarta.equals("J")) {
			posXEsqInfIzquierda = posXdeCarta + anchoCarta - 17;
			posYEsqInfIzquierda = posYdeCarta + alturaCarta - 13;
		} else if (nombreCarta.equals("Q"))
			posXEsqInfIzquierda = posXdeCarta + anchoCarta - 26;
		else if (nombreCarta.equals("K")) {
			posXEsqInfIzquierda = posXdeCarta + anchoCarta - 26;
			posYEsqInfIzquierda = posYdeCarta + alturaCarta - 10;
		} else if (nombreCarta.equals("Joker"))
			posXEsqInfIzquierda = posXdeCarta + 11;
		else
			posYEsqInfIzquierda = posYdeCarta + alturaCarta - 10;
		mesa.dibujarString(nombreCarta, posXEsqInfIzquierda, posYEsqInfIzquierda, color);
	}

	/**
	 * Metodo con el que se mostrara graficamente las cartas volteadas que vayan
	 * apareciendo en la mano del crupier
	 */
	//@ requires mesa != null;
	//@ requires 0 < mesa.XMAX < Integer.MAX_VALUE;
	//@ requires 0 < mesa.YMAX < Integer.MAX_VALUE;
	//@ requires 0 <= (posXdeCarta + 4) < Integer.MAX_VALUE;
	//@ requires 0 <= (posYdeCarta + 5) < Integer.MAX_VALUE;
	//@ requires 30 <= alturaCarta <= 10000;
	//@ requires 30 <= anchoCarta <= 10000;
	//@ requires (posXdeCarta + anchoCarta) < Integer.MAX_VALUE;
	//@ requires (posYdeCarta + alturaCarta) < Integer.MAX_VALUE;
	//@ requires (posXdeCarta + (anchoCarta / 2) + 25) < Integer.MAX_VALUE;
	//@ requires (posYdeCarta + (alturaCarta / 2) + 18) < Integer.MAX_VALUE;
	public static void dibujarCartaVolteada(MaquinaDeTrazados mesa, int posXdeCarta, int posYdeCarta,
			int alturaCarta, int anchoCarta) {
		// Dibujar el rectangulo externo e interno de la carta volteada
		Colores color = Colores.ORANGE;
		mesa.dibujarRectanguloLleno(posXdeCarta, posYdeCarta, 72, 108, Colores.DARK_GRAY);
		mesa.dibujarRectangulo(posXdeCarta + 4, posYdeCarta + 5, anchoCarta - 10, alturaCarta - 10, color);

		// Arreglos para las coordenadas de los triangulos y rombos del patron central
		int[] xPuntos1 = new int[] { posXdeCarta + (anchoCarta / 2) - 12, posXdeCarta + (anchoCarta / 2) - 1,
				posXdeCarta + (anchoCarta / 2) + 11, posXdeCarta + (anchoCarta / 2) - 1 };
		int[] yPuntos1 = new int[] { posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) - 19,
				posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) + 19 };
		int[] xPuntos2 = new int[] { posXdeCarta + (anchoCarta / 2) - 23, posXdeCarta + (anchoCarta / 2) - 12,
				posXdeCarta + (anchoCarta / 2) - 1 };
		int[] xPuntos3 = new int[] { posXdeCarta + (anchoCarta / 2) + 21, posXdeCarta + (anchoCarta / 2) + 10,
				posXdeCarta + (anchoCarta / 2) - 1 };
		int[] yPuntos2 = new int[] { posYdeCarta + (alturaCarta / 2) - 19, posYdeCarta + (alturaCarta / 2),
				posYdeCarta + (alturaCarta / 2) - 19 };
		int[] yPuntos3 = new int[] { posYdeCarta + (alturaCarta / 2) + 19, posYdeCarta + (alturaCarta / 2),
				posYdeCarta + (alturaCarta / 2) + 19 };
		int[] xPuntos4 = new int[] { posXdeCarta + (anchoCarta / 2) - 23, posXdeCarta + (anchoCarta / 2) - 15,
				posXdeCarta + (anchoCarta / 2) - 7, posXdeCarta + (anchoCarta / 2) - 15 };
		int[] xPuntos5 = new int[] { posXdeCarta + (anchoCarta / 2) + 23, posXdeCarta + (anchoCarta / 2) + 15,
				posXdeCarta + (anchoCarta / 2) + 7, posXdeCarta + (anchoCarta / 2) + 15 };
		int[] yPuntos4 = new int[] { posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) - 8,
				posYdeCarta + (alturaCarta / 2), posYdeCarta + (alturaCarta / 2) + 8 };

		// Dibujar el patron central del reverso de las cartas
		mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 7, posYdeCarta + (alturaCarta / 2) - 6, 13, 13,
				color);
		mesa.dibujarOvalo(posXdeCarta + (anchoCarta / 2) - 9, posYdeCarta + (alturaCarta / 2) - 8, 17, 17,
				color);
		mesa.dibujarPoligono(xPuntos1, yPuntos1, 4, color);
		mesa.dibujarLinea(posXdeCarta + (anchoCarta / 2) - 23, posYdeCarta + (alturaCarta / 2) - 4,
				posXdeCarta + (anchoCarta / 2) + 22, posYdeCarta + (alturaCarta / 2) - 4, color);
		mesa.dibujarLinea(posXdeCarta + (anchoCarta / 2) - 27, posYdeCarta + (alturaCarta / 2),
				posXdeCarta + (anchoCarta / 2) + 25, posYdeCarta + (alturaCarta / 2), color);
		mesa.dibujarLinea(posXdeCarta + (anchoCarta / 2) - 23, posYdeCarta + (alturaCarta / 2) + 4,
				posXdeCarta + (anchoCarta / 2) + 22, posYdeCarta + (alturaCarta / 2) + 4, color);
		mesa.dibujarPoligono(xPuntos2, yPuntos2, 3, color);
		mesa.dibujarPoligono(xPuntos2, yPuntos3, 3, color);
		mesa.dibujarPoligono(xPuntos3, yPuntos2, 3, color);
		mesa.dibujarPoligono(xPuntos3, yPuntos3, 3, color);
		mesa.dibujarPoligonoLleno(xPuntos4, yPuntos4, 4, color);
		mesa.dibujarPoligonoLleno(xPuntos5, yPuntos4, 4, color);

		// Arreglos para las coordenadas de los rombos de los patrones superiores e
		// inferiores
		int[] xPuntos6 = new int[] { posXdeCarta + (anchoCarta / 2) - 17, posXdeCarta + (anchoCarta / 2) - 12,
				posXdeCarta + (anchoCarta / 2) - 7, posXdeCarta + (anchoCarta / 2) - 12 };
		int[] xPuntos7 = new int[] { posXdeCarta + (anchoCarta / 2) + 17, posXdeCarta + (anchoCarta / 2) + 12,
				posXdeCarta + (anchoCarta / 2) + 7, posXdeCarta + (anchoCarta / 2) + 12 };
		int[] yPuntos6 = new int[] { posYdeCarta + 14, posYdeCarta + 9,
				posYdeCarta + 14, posYdeCarta + 19 };
		int[] yPuntos7 = new int[] { posYdeCarta + alturaCarta - 16, posYdeCarta + alturaCarta - 21,
				posYdeCarta + alturaCarta - 16, posYdeCarta + alturaCarta - 11 };

		// Dibujar el patron superior del reverso de las cartas
		mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 4, posYdeCarta + 11, 7, 7,
				color);
		mesa.dibujarOvalo(posXdeCarta + (anchoCarta / 2) - 6, posYdeCarta + 9, 11, 11,
				color);
		mesa.dibujarPoligonoLleno(xPuntos6, yPuntos6, 4, color);
		mesa.dibujarPoligonoLleno(xPuntos7, yPuntos6, 4, color);

		// Dibujar el patron inferior del reverso de las cartas
		mesa.dibujarOvaloLleno(posXdeCarta + (anchoCarta / 2) - 4, posYdeCarta + alturaCarta - 19, 7, 7,
				color);
		mesa.dibujarOvalo(posXdeCarta + (anchoCarta / 2) - 6, posYdeCarta + alturaCarta - 21, 11, 11,
				color);
		mesa.dibujarPoligonoLleno(xPuntos6, yPuntos7, 4, color);
		mesa.dibujarPoligonoLleno(xPuntos7, yPuntos7, 4, color);
	}

    public static void main(String[] args) {
        // Se crea un mazo con todas las 56 posibles cartas
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
            Carta.J_CORAZON, Carta.Q_CORAZON, Carta.K_CORAZON, Carta.COMODÍN_CORAZON
        };

        // Se declaran e inicializan las variables basicas que se usaran en el programa
        Console con = System.console();
        Carta jugador[] = new Carta[21];
        Carta crupier[] = new Carta[17];
        int credito = 100;
		int apuesta = 0;
        int puntosJugador = 0;
        int puntosCrupier = 0;
		int opcion = 0;
		int mensaje = 0;
		int comprobante = 0;
		int cota_FM = 0;
		int maxJugadas = 0;
		boolean salir_juego = false;
		boolean fin_mano = false;

        // Se especifican las dimensiones de las cartas
		int alturaCarta = 108;
		int anchoCarta = 72;
        // Se especifica la resolucion de la ventana de la interfaz grafica
		int alturaMesa = 774;
		int anchoMesa = 1278;

		// Se crea el panel de la Maquina de Trazados. El color gris crea un fondo agradable
		MaquinaDeTrazados mesa = new MaquinaDeTrazados(anchoMesa, alturaMesa, "BlackJack", Colores.GRAY);

        // Semicirculo verde que imita una mesa de BlackJack real con un borde oscuro
        mesa.dibujarOvaloLleno(1, -(anchoMesa / 2), anchoMesa, anchoMesa, Colores.DARK_GRAY);
        mesa.dibujarOvaloLleno(11, -(anchoMesa / 2), anchoMesa - 20, anchoMesa - 20, Colores.GREEN);

        // Mensaje de bienvenida donde se le pregunta el nombre al jugador
        System.out.println("¡Desafia a la computadora en Blackjack!");
        System.out.println("Desarrollado por Isea, Luis (19-10175) y Prieto, Jesus (19-10211).");
        System.out.println("");
        String nombre = con.readLine("Por favor, ingrese su nombre: ");
        System.out.println("Es un placer tenerte aqui, " + nombre + ".");
        System.out.println("");

        // Se le explica al jugador el sistema de creditos y apuestas
        // Luego se le pide al jugador que ingrese el monto de la apuesta usando su nombre
        System.out.println("Posees 100 creditos por empezar a jugar. La apuesta minima por mano son 10 creditos.");
        
		while (!salir_juego && credito >= 10 && maxJugadas != 5) {
			apuesta = obtenerApuesta(credito, nombre);
			credito = operacionCredito(apuesta, credito, 1);

			// Una vez se tiene el monto que aposto el jugador, se reparten las cartas al azar
			int i = 0;
			int j = 0;
			while (i <= 2) {
				if(i == 2)
					break;
				jugador[i] = darCarta(mazo);
				crupier[i] = darCarta(mazo);
				i++;
				j++;
			}

			// Luego se dibujan las cartas del crupier
			dibujarCartaVisible(mesa, (anchoMesa / 2) - 82, 50, alturaCarta, anchoCarta, obtenerPaloCarta(crupier[0]), obtenerNombreCarta(crupier[0]));
			dibujarCartaVolteada(mesa, (anchoMesa / 2) + 10, 50, alturaCarta, anchoCarta);

			// E inmediatamente se dibujan las cartas del jugador
			dibujarCartaVisible(mesa, (anchoMesa / 2) - 82, 300, alturaCarta, anchoCarta, obtenerPaloCarta(jugador[0]),  obtenerNombreCarta(jugador[0]));
			dibujarCartaVisible(mesa, (anchoMesa / 2) + 10, 300, alturaCarta, anchoCarta, obtenerPaloCarta(jugador[1]),  obtenerNombreCarta(jugador[1]));
			mesa.mostrar();

			// Calculamos el valor de las manos en la mesa
			puntosJugador = valorMano(jugador, 2, puntosJugador);
			puntosCrupier = valorMano(crupier, 2, puntosCrupier);

			// Se le muestra al jugador el valor de las cartas en la mesa en la interfaz grafica
			mesa.configurarFuente("SansSerif", Font.BOLD, 18);
			mesa.dibujarString("Carta descubierta del crupier: " + Integer.toString(obtenerValorCarta(crupier[0])), (anchoMesa / 2) - 160, 30, Colores.DARK_GRAY);
			mesa.dibujarString("Mano actual: " + Integer.toString(puntosJugador), (anchoMesa / 2) - 82, 280, Colores.DARK_GRAY);

			// Se le muestra al jugador en la interfaz grafica el numero de creditos totales
			// que posee y tambien cuantos se apostaron en la mano actual
			mesa.dibujarString("Creditos actuales: " + Integer.toString(credito), (anchoMesa / 2) - 410, 210, Colores.BLUE);
			mesa.dibujarString("Creditos apostados: " + Integer.toString(apuesta), (anchoMesa / 2) + 190, 210, Colores.RED);

			// Se le muestra al jugador el valor de las cartas en la mesa en la interfaz de texto
			System.out.println("");
			System.out.println("Valor de la carta descubierta del crupier: " + obtenerValorCarta(crupier[0]));
			System.out.println("Valor de la mano actual: " + puntosJugador);
			System.out.println("");
			
			while (!fin_mano) {
				// Acciones del jugador 

				//Verificar si tiene BLACKJACK o empato
				if (puntosJugador == 21 && puntosCrupier != 21) {
					credito = ganancia(apuesta, credito, 1);
					mensaje = mensajeJugador(puntosJugador, puntosCrupier);
					// Indicar que gano el jugador
				} else if (puntosJugador == puntosCrupier) {
					mensaje = mensajeJugador(puntosJugador, puntosCrupier);
					credito = operacionCredito(apuesta, credito, 2);
				}

				opcion = opciones(nombre);
				while (opcion == 1){
					// el jugador pide una carta
					jugador[i] = darCarta(mazo);
					i++;
					// Calculo del puntaje
					puntosJugador = valorMano(jugador, i, puntosJugador);

					// Verificion del puntaje
					mensaje = mensajeJugador(puntosJugador, puntosCrupier);
					if (mensaje == 1){
						break;
					} else if (mensaje == 2) {
						credito = apuesta + credito;
						break;
					} else if (mensaje == 3) {
						credito = ganancia(apuesta, credito, 1);
						break;
					}
					opcion = opciones(nombre);
				}

				// Verificacion si el jugador gano, empato o perdio
				if (mensaje == 1 || mensaje == 2 || mensaje == 3)
					break;
				else if (puntosJugador <= 21) {
					if (opcion == 2) {
						// El jugador se planta
						// Actualizar estado
					}else if (opcion == 3) {
						// El jugador dobla la apuesta
						comprobante = doblarApuesta(puntosJugador, puntosCrupier, apuesta, credito);
						if (comprobante != apuesta ) {
							apuesta = comprobante;
							jugador[i] = darCarta(mazo);
							i++;
							puntosJugador = valorMano(jugador, i, puntosJugador);
							credito = operacionCredito(apuesta, credito, 3);
							mensaje = mensajeJugador(puntosJugador, puntosCrupier);
							if (mensaje == 1){
								break;
							} else if (mensaje == 2) {
								credito = operacionCredito(apuesta, credito, 2);
								break;
							} else if (mensaje == 3) {
								credito = ganancia(apuesta, credito, 1);
								break;
								
							}else
								puntosJugador = puntosJugador;
						}	
					}else {
						// El jugador decide salirse del juego
						salir_juego = true;
						break;
					}
					
				}else if (puntosJugador > 21){
					//el jugador sobrepaso los 21 
					mensaje = mensajeJugador(puntosJugador, puntosCrupier);
					break;
				}

				//Acciones del crupier
				while (puntosCrupier < 17) {
					//dar carta
					crupier[j] = darCarta(mazo);
					j++;
					puntosCrupier = valorMano(crupier, j, puntosCrupier);
				}
				if (17 <= puntosCrupier && puntosCrupier <= 21) {
					// Plantarse
					// Skip
					// Actualizar 
				} else {
					// presentar perdida del crupier
					mensaje = mensajeCrupier(puntosCrupier);
					break;
				}

				//Decision del Juego
				mensaje = decision(puntosJugador, puntosCrupier);
				if (mensaje == 3) {
					// Retornar la apuesta, hubo empate
					credito = ganancia(apuesta, credito, 3); 
				} else if (mensaje == 2) {
					// Jugador gana con una relacion 1:1
					credito = ganancia(apuesta, credito, 2);
				} else if (mensaje == 1) {
					// Jugador pierde y no se le devuelve le dinero
					credito = ganancia(apuesta, credito, 4);
					//actualizar estado y componente grafico
				}
				break;
			}
			System.out.println("¿Deseas jugar otro mano?");
			System.out.println("Para SI escribe 1");
			System.out.println("Para NO escribe 0");
			cota_FM = Integer.parseInt(con.readLine("Y/N:"));
			if (cota_FM == 1){
				maxJugadas++;
				puntosJugador = 0;
        		puntosCrupier = 0;
				opcion = 0;
				mensaje = 0;
				comprobante = 0;
				cota_FM = 0;
			} else
				break;

			if (maxJugadas == 5)
				System.out.println("Haz alcanzado la maxima cantidad de jugadas disponibles");
		}
		System.out.println("El juego se ha terminado");
		mesa.terminar();
    }
}

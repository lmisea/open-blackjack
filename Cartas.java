import java.awt.Font;
import java.util.Random;

public class Cartas {

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
	 * Metodo que permite calcular el valor de la suma de las cartas de una mano
     */
    //@ requires 0 <= numCartasMano <= manoCartas.length;
    //@ ensures 2 <= \result || \result <= 31;
    public static /*@ pure @*/ int valorMano(/*@ non_null */ Carta /*@ non_null */[] manoCartas, int numCartasMano) {
        int puntosMano = 0;

        //@ maintaining 0 <= numCartasMano <= manoCartas.length;
        //@ maintaining (\forall int k; 0 <= k && k < numCartasMano; manoCartas[k].ordinal() % 14 >= 1 || manoCartas[k].ordinal() % 14 <= 11);
        //@ decreases numCartasMano;
        while (numCartasMano != 0) {
            numCartasMano -= 1;
            //@ assume 0 <= numCartasMano <= 21;
            //@ assume 0 <= puntosMano <= 31;
            if (manoCartas[numCartasMano].ordinal() % 14 <= 9)
                puntosMano = (manoCartas[numCartasMano].ordinal() % 14) + 1 + puntosMano;
            else if (manoCartas[numCartasMano].ordinal() % 14 <= 12)
                puntosMano = 10 + puntosMano ;
            else
                puntosMano = 11 + puntosMano;
            //@ assert puntosMano >= 2 || puntosMano <= 31;
        }
        //@ assert puntosMano >= 2 || puntosMano <= 31;
        return puntosMano;
    }

	/**
	 * Metodo con el que se determina si el color del palo y el texto de la carta
	 * sera negro o rojo. A Picas y a Treboles se les asigna el color negro.
	 * Mientras que a Diamantas y a Corazones se les asigna el color rojo
	 */
	//@ requires (paloCarta.equals("Picas") || paloCarta.equals("Diamantes") || paloCarta.equals("Treboles") || paloCarta.equals("Corazones"));
	//@ ensures (\result == Colores.BLACK) <== (paloCarta.equals("Picas") || paloCarta.equals("Treboles"));
	//@ ensures (\result == Colores.RED) <== (paloCarta.equals("Diamantes") || paloCarta.equals("Corazones"));
	public static /*@ pure @*/ Colores determinarColorCarta(String paloCarta) {
		if (paloCarta.equals("Picas") || paloCarta.equals("Treboles"))
			return Colores.BLACK;
		else
			return Colores.RED;
	}

	/**
	 * Metodo con el que se determina cuantas cartas deben ir por fila a la
	 * hora de dibujarlas en la mesa de BlackJack. El objetivo es aprovechar
	 * el espacio de la mesa y no agrupar todas las cartas en una sola fila
	 */
	//@ requires 0 <= numCartasMano <= 21;
	//@ requires poseedorMano.equals("crupier") || poseedorMano.equals("jugador");
	//@ ensures \result != null;
	//@ ensures \result instanceof int[];
	//@ ensures \result.length == 3;
	public static /*@ pure @*/ int[] getSizes(int numCartasMano, String poseedorMano) {
		int[] sizes = new int[3];
		if (poseedorMano.equals("crupier")) {
			if (numCartasMano <= 12)
				sizes[0] = numCartasMano;
			else {
				sizes[0] = 12;
				sizes[1] = numCartasMano - 12;
			}
		} else {
			if (numCartasMano <= 10)
				sizes[0] = numCartasMano;
			else if (numCartasMano <= 18) {
				sizes[0] = 10;
				sizes[1] = numCartasMano - 10;
			} else {
				sizes[0] = 10;
				sizes[1] = 8;
				sizes[2] = numCartasMano - 18;
			}
		}
		return sizes;
	}

	/**
	 * Metodo con el que dado el numero de cartas de una mano, se construye un
	 * arreglo que determina la posicion X de cada una de las cartas
	 */
	//@ requires 0 <= numCartasMano <= 21;
	//@ requires 30 <= anchoCarta <= 10000;
	//@ requires 0 < anchoMesa < Integer.MAX_VALUE;
	//@ ensures \result != null;
	//@ ensures \result instanceof int[];
	//@ ensures \result.length == numCartasMano;
	public static /*@ pure @*/ int[] posicionesManoCarta(int numCartasMano, int anchoCarta, int anchoMesa) {
		int espacio = 20;
		int bloque = anchoCarta + espacio;
		int[] posicionesXdeCartas = new int[numCartasMano];
		int i = 0;
		//@ maintaining 0 <= i <= numCartasMano;
		//@ decreases numCartasMano - i;
		while (i < numCartasMano) {
			if (numCartasMano % 2 == 0) {
				//@ assume Integer.MIN_VALUE < i - (numCartasMano / 2) < Integer.MAX_VALUE;
				int posicion = i - (numCartasMano / 2);
				//@ assume Integer.MIN_VALUE < (anchoMesa / 2) + (bloque * posicion) + (espacio / 2) < Integer.MAX_VALUE;
				posicionesXdeCartas[i] = (anchoMesa / 2) + (bloque * posicion) + (espacio / 2);
			} else {
				//@ assume Integer.MIN_VALUE < i - ((numCartasMano - 1 )/ 2) < Integer.MAX_VALUE;
				int posicion = i - ((numCartasMano - 1) / 2);
				//@ assume Integer.MIN_VALUE < (anchoMesa / 2) + (bloque * posicion) - (anchoCarta / 2) < Integer.MAX_VALUE;
				posicionesXdeCartas[i] = (anchoMesa / 2) + (bloque * posicion) - (anchoCarta / 2);
			}
			i = i + 1;
		}
		return posicionesXdeCartas;
	}

	/**
	 * Metodo con el que se dibujara una mesa de BlackJack, con un semicirculo verde
	 * que imite las mesas de BlackJack reales. Tambien se dibujaran las zonas
	 * que delimitan donde van las cartas del jugador y donde las del crupier
	 */
	//@ requires mesa != null;
	//@ requires 0 < anchoMesa <= mesa.XMAX < Integer.MAX_VALUE;
	//@ requires 0 < alturaMesa <= mesa.YMAX < Integer.MAX_VALUE;
	//@ requires 30 <= alturaCarta <= 10000;
	//@ requires 30 <= anchoCarta <= 10000;
	public static /*@ pure @*/ void dibujarMesaBlackjack(MaquinaDeTrazados mesa, int anchoMesa, int alturaMesa, int alturaCarta,
		int anchoCarta) {
		// Semicírculo verde que imita una mesa de BlackJack real con un borde oscuro
		mesa.dibujarOvaloLleno(1, -(anchoMesa / 2), anchoMesa, anchoMesa, Colores.DARK_GRAY);
		mesa.dibujarOvaloLleno(9, -(anchoMesa / 2), anchoMesa - 16, anchoMesa - 16, Colores.GREEN);

		// Dibujar la zona que delimita donde van las cartas del jugador
		mesa.dibujarOvalo(57, -(anchoMesa / 2), anchoMesa - 112, anchoMesa - 20, Colores.RED);
		int[] xPuntos = new int[] {35, 70 , anchoMesa - 35, anchoMesa - 70};
		int[] yPuntos = new int[] {-5, 258 , -5, 258};
		mesa.dibujarPoligonoLleno(xPuntos, yPuntos, 4, Colores.GREEN);
		mesa.dibujarLinea(110, 250, anchoMesa - 108, 250, Colores.RED);
		mesa.configurarFuente("SansSerif", Font.BOLD, 24);
		mesa.dibujarString("Jugador", 385, 535, Colores.RED);
		mesa.dibujarString("Jugador", anchoMesa - 487, 535, Colores.RED);

		// Dibujar la zona que delimita donde van las cartas del crupier
		int[] xPuntos2 = new int[] {85, 85 , 405, 405, anchoMesa - 405, anchoMesa - 405, anchoMesa - 85, anchoMesa - 85};
		int[] yPuntos2 = new int[] {5, 123, 123, 244, 244, 123, 123, 5};
		mesa.dibujarPoligono(xPuntos2, yPuntos2, 8, Colores.BLACK);
		mesa.dibujarString("Crupier", 280, 192, Colores.BLACK);
		mesa.dibujarString("Crupier", anchoMesa - 385, 192, Colores.BLACK);

		// Escribir BlackJack debajo del semicirculo verde
		mesa.configurarFuente("SansSerif", Font.BOLD, 38);
		mesa.dibujarString("Black", (anchoMesa / 2) - 110, alturaMesa - 80, Colores.BLACK);
		mesa.dibujarString("Jack", (anchoMesa / 2) + 10, alturaMesa - 80, Colores.RED);

		// Dibujar los cuatro palos de las cartas de blackjack centrados debajo del BlackJack central
		//@ assume 0 < (anchoMesa / 2) - 110 < Integer.MAX_VALUE;
		//@ assume 0 < alturaMesa - 100 < Integer.MAX_VALUE;
		//@ assume alturaMesa - 100 + alturaCarta < Integer.MAX_VALUE;
		dibujarPaloCarta(mesa, (anchoMesa / 2) - 110, alturaMesa - 100, alturaCarta, anchoCarta, "Picas", Colores.BLACK);
		dibujarPaloCarta(mesa, (anchoMesa / 2) - 65, alturaMesa - 100, alturaCarta, anchoCarta, "Diamantes", Colores.RED);
		dibujarPaloCarta(mesa, (anchoMesa / 2) - 20, alturaMesa - 100, alturaCarta, anchoCarta, "Treboles", Colores.BLACK);
		dibujarPaloCarta(mesa, (anchoMesa / 2) + 25, alturaMesa - 100, alturaCarta, anchoCarta, "Corazones", Colores.RED);
	}

	/**
	 * Metodo con el que se dibuja el simbolo del palo de la carta.
	 * El simbolo que se dibujara estara centrado
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
	//@ requires color == Colores.BLACK || color == Colores.RED;
	public static /*@ pure @*/ void dibujarPaloCarta(MaquinaDeTrazados mesa, int posXdeCarta, int posYdeCarta,
			int alturaCarta, int anchoCarta, String paloCarta, Colores color) {
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
	}

	/**
	 * Metodo con el que se dibuja la forma rectangular de la carta en un color blanco
	 * y, a su vez, se dibuja el rectangulo interior que delimita el texto de la carta.
	 * Tambien con este metodo se escribira el nombre de la carta en las esquinas superior
	 * izquierda e inferior derecha. El nombre de la carta se refiere al "A", 2, 5, "J", "K", etc
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
	//@ requires nombreCarta.equals("A") || nombreCarta.equals("J") || nombreCarta.equals("Q") || nombreCarta.equals("K") || nombreCarta.equals("Joker") || nombreCarta.equals("2") || nombreCarta.equals("3") || nombreCarta.equals("4") || nombreCarta.equals("5") || nombreCarta.equals("6") || nombreCarta.equals("7") || nombreCarta.equals("8") || nombreCarta.equals("9") || nombreCarta.equals("10");
	//@ requires color == Colores.BLACK || color == Colores.RED;
	public static /*@ pure @*/ void dibujarCartaConNombre(MaquinaDeTrazados mesa, int posXdeCarta, int posYdeCarta,
			int alturaCarta, int anchoCarta, String nombreCarta, Colores color) {
		// Dibujar el rectángulo externo e interno de la carta
		mesa.dibujarRectanguloLleno(posXdeCarta, posYdeCarta, 72, 108, Colores.WHITE);
		mesa.dibujarRectangulo(posXdeCarta + 4, posYdeCarta + 5, anchoCarta - 10, alturaCarta - 10, Colores.DARK_GRAY);

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

	/**
	 * Metodo con el que se mostrara graficamente los valores de las manos
	 * del crupier y del jugador en la esquina inferior izquierda
	 */
	//@ requires mesa != null;
	//@ requires 0 < mesa.XMAX < Integer.MAX_VALUE;
	//@ requires 0 < mesa.YMAX < Integer.MAX_VALUE;
	//@ requires 0 <= alturaMesa < Integer.MAX_VALUE;
	//@ requires 0 <= valorManoCrupier <= 31;
	//@ requires 0 <= valorManoJugador <= 31;
	public static /*@ pure @*/ void mostrarPuntuaciones(MaquinaDeTrazados mesa, int alturaMesa,
		boolean mostrarCartasCrupier, int valorManoCrupier, int valorManoJugador) {
		String puntuacionCrupier = Integer.toString(valorManoCrupier);
		String puntuacionJugador = Integer.toString(valorManoJugador);
		mesa.configurarFuente("SansSerif", Font.BOLD, 22);
		if (mostrarCartasCrupier == false)
			mesa.dibujarString("Valor carta visible del crupier: " + puntuacionCrupier, 30, alturaMesa - 85, Colores.BLACK);
		else
			mesa.dibujarString("Valor mano del crupier: " + puntuacionCrupier, 30, alturaMesa - 85, Colores.BLACK);
		mesa.dibujarString("Valor mano del jugador: " + puntuacionJugador, 30, alturaMesa - 35, Colores.RED);
	}

	/**
	 * Metodo con el que se mostrara graficamente la cantidad de creditos
	 * que posee el jugador y la cantidad de creditos que se aposto en la mano.
	 * Estas se muestran en la esquina inferior derecha
	 */
	//@ requires mesa != null;
	//@ requires 0 < mesa.XMAX < Integer.MAX_VALUE;
	//@ requires 0 < mesa.YMAX < Integer.MAX_VALUE;
	//@ requires 0 <= alturaMesa < Integer.MAX_VALUE;
	//@ requires 0 <= anchoMesa < Integer.MAX_VALUE;
	//@ requires 0 <= creditosActuales <= 10000;
	//@ requires 10 <= apuestaMano<= creditosActuales;
	public static /*@ pure @*/ void mostrarCreditos(MaquinaDeTrazados mesa, int anchoMesa, int alturaMesa,
		int creditosActuales, int apuestaMano) {
		String creditosTotales = Integer.toString(creditosActuales);
		String creditosApostados = Integer.toString(apuestaMano);
		mesa.configurarFuente("SansSerif", Font.BOLD, 22);
		mesa.dibujarString("Total de creditos restantes: " + creditosTotales, anchoMesa - 425, alturaMesa - 85, Colores.BLACK);
		mesa.dibujarString("Creditos apostados: " + creditosApostados, anchoMesa - 325, alturaMesa - 35, Colores.RED);
	}

	//@ ensures \result != null;
	//@ ensures \result.length == 56;
	public static /*@ pure @*/ Carta[] repartirCartasEnElMazo() {
		Carta[] mazo = new Carta[] {
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
		return mazo;
	}

	public static void main(String[] args) {
        // Se crea un mazo con todas las 56 posibles cartas
        Carta mazo[] = new Carta[56];
		mazo = repartirCartasEnElMazo();

        // Se declaran e inicializan las variables basicas que se usaran en el programa
        Carta jugador[] = new Carta[21];
        Carta crupier[] = new Carta[17];

		// Resolución de la ventana donde se ejecutará el juego de BlackJack
		int alturaCarta = 108;
		int anchoCarta = 72;
		int alturaMesa = 774;
		int anchoMesa = 1278;

		// Panel de la Máquina de Trazados. El color gris crea un fondo agradable
		MaquinaDeTrazados mesa = new MaquinaDeTrazados(anchoMesa, alturaMesa, "BlackJack", Colores.GRAY);

		// Dibujar la mesa de blackjack
		dibujarMesaBlackjack(mesa, anchoMesa, alturaMesa, alturaCarta, anchoCarta);

		// Se reparten las cartas al azar
		int i = 0;
		while (i < 17) {
			crupier[i] = darCarta(mazo);
			i++;
		}
		i = 0;
		while (i < 21) {
			jugador[i] = darCarta(mazo);
			i++;
		}

		// Dibujar las cartas del crupier. La primera visible y el resto volteadas
		i = 0;
		int j = 0;
		int numCartasCrupier = 17;
		int[] sizes = new int[3];
		boolean mostrarCartasCrupier = true;
		int valorManoCrupier = 0;
		sizes = getSizes(numCartasCrupier, "crupier");
		while (i < numCartasCrupier) {
			int[] posicionesXdeCartas = new int[sizes[0]];
			int[] posicionesXdeCartas2 = new int[sizes[1]];
			posicionesXdeCartas = posicionesManoCarta(sizes[0], anchoCarta, anchoMesa);
			posicionesXdeCartas2 = posicionesManoCarta(sizes[1], anchoCarta, anchoMesa);
			String paloCarta = obtenerPaloCarta(crupier[i]);
			Colores color = determinarColorCarta(paloCarta);
			String nombreCarta = obtenerNombreCarta(crupier[i]);
			if (mostrarCartasCrupier == false) {
				if (i == 0) {
					dibujarCartaConNombre(mesa, posicionesXdeCartas[i], 10, alturaCarta, anchoCarta, nombreCarta, color);
					dibujarPaloCarta(mesa, posicionesXdeCartas[i], 10, alturaCarta, anchoCarta, paloCarta, color);
				} else if (i < 12)
					dibujarCartaVolteada(mesa, posicionesXdeCartas[i], 10, alturaCarta, anchoCarta);
				else {
					dibujarCartaVolteada(mesa, posicionesXdeCartas2[j], 128, alturaCarta, anchoCarta);
					j = j + 1;
				}
				valorManoCrupier = obtenerValorCarta(crupier[0]);
			} else {
				if (i < 12) {
					dibujarCartaConNombre(mesa, posicionesXdeCartas[i], 10, alturaCarta, anchoCarta, nombreCarta, color);
					dibujarPaloCarta(mesa, posicionesXdeCartas[i], 10, alturaCarta, anchoCarta, paloCarta, color);
				} else {
					dibujarCartaConNombre(mesa, posicionesXdeCartas2[j], 128, alturaCarta, anchoCarta, nombreCarta, color);
					dibujarPaloCarta(mesa, posicionesXdeCartas2[j], 128, alturaCarta, anchoCarta, paloCarta, color);
					j = j + 1;
				}
				valorManoCrupier = valorMano(crupier, numCartasCrupier);
			}
			i = i + 1;
		}

		// Dibujar las cartas del jugador, todas visibles
		i = j = 0;
		int k = 0;
		int numCartasJugador = 21;
		int valorManoJugador = valorMano(jugador, numCartasJugador);
		sizes = getSizes(numCartasJugador, "jugador");
		while (i < numCartasJugador) {
			int[] posicionesXdeCartas = new int[sizes[0]];
			int[] posicionesXdeCartas2 = new int[sizes[1]];
			int[] posicionesXdeCartas3 = new int[sizes[2]];
			posicionesXdeCartas = posicionesManoCarta(sizes[0], anchoCarta, anchoMesa);
			posicionesXdeCartas2 = posicionesManoCarta(sizes[1], anchoCarta, anchoMesa);
			posicionesXdeCartas3 = posicionesManoCarta(sizes[2], anchoCarta, anchoMesa);
			String paloCarta = obtenerPaloCarta(jugador[i]);
			Colores color = determinarColorCarta(paloCarta);
			String nombreCarta = obtenerNombreCarta(jugador[i]);
			if (i < 10) {
				dibujarCartaConNombre(mesa, posicionesXdeCartas[i], 256, alturaCarta, anchoCarta, nombreCarta, color);
				dibujarPaloCarta(mesa, posicionesXdeCartas[i], 256, alturaCarta, anchoCarta, paloCarta, color);
			} else if (i < 18) {
				dibujarCartaConNombre(mesa, posicionesXdeCartas2[j], 374, alturaCarta, anchoCarta, nombreCarta, color);
				dibujarPaloCarta(mesa, posicionesXdeCartas2[j], 374, alturaCarta, anchoCarta, paloCarta, color);
				j = j + 1;
			} else {
				dibujarCartaConNombre(mesa, posicionesXdeCartas3[k], 492, alturaCarta, anchoCarta, nombreCarta, color);
				dibujarPaloCarta(mesa, posicionesXdeCartas3[k], 492, alturaCarta, anchoCarta, paloCarta, color);
				k = k + 1;
			}
			i = i + 1;
		}

		mostrarPuntuaciones(mesa, alturaMesa, mostrarCartasCrupier, valorManoCrupier, valorManoJugador);
		mostrarCreditos(mesa, anchoMesa, alturaMesa, 90, 10);

		mesa.mostrar();
	}
}

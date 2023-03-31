import java.awt.Font;

public class Cartas {

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
	//@ requires paloCarta.length() > 0;
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
		// Resolución de la ventana donde se ejecutará el juego de BlackJack
		int alturaCarta = 108;
		int anchoCarta = 72;
		int alturaMesa = 774;
		int anchoMesa = 1278;

		// Panel de la Máquina de Trazados. El color gris crea un fondo agradable
		MaquinaDeTrazados mesa = new MaquinaDeTrazados(anchoMesa, alturaMesa, "OpenJML BlackJack", Colores.GRAY);

		// Semicírculo verde que imita una mesa de BlackJack real con un borde oscuro
		mesa.dibujarOvaloLleno(1, -(anchoMesa / 2), anchoMesa, anchoMesa, Colores.DARK_GRAY);
		mesa.dibujarOvaloLleno(11, -(anchoMesa / 2), anchoMesa - 20, anchoMesa - 20, Colores.GREEN);

		// Cartas del crupier
		dibujarCartaVisible(mesa, (anchoMesa / 2) - 174, 20, alturaCarta, anchoCarta, "Picas", "Q");
		dibujarCartaVolteada(mesa, (anchoMesa / 2) - 82, 20, alturaCarta, anchoCarta);
		dibujarCartaVolteada(mesa, (anchoMesa / 2) + 10, 20, alturaCarta, anchoCarta);
		dibujarCartaVolteada(mesa, (anchoMesa / 2) + 102, 20, alturaCarta, anchoCarta);

		// Cartas del jugador
		dibujarCartaVisible(mesa, (anchoMesa / 2) - 174, 280, alturaCarta, anchoCarta, "Picas", "J");
		dibujarCartaVisible(mesa, (anchoMesa / 2) - 82, 280, alturaCarta, anchoCarta, "Diamantes", "A");
		dibujarCartaVisible(mesa, (anchoMesa / 2) + 10, 280, alturaCarta, anchoCarta, "Treboles", "Joker");
		dibujarCartaVisible(mesa, (anchoMesa / 2) + 102, 280, alturaCarta, anchoCarta, "Corazones", "10");

		mesa.mostrar();
	}
}
